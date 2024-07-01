'import LinearAlgebra.Vector

-- void encoder_forward(float* out,
--                    int* inp, float* wte, float* wpe,
--                    int B, int T, int C) {
--     // out is (B,T,C). At each position (b,t), a C-dimensional vector summarizing token & position
--     // inp is (B,T) of integers, holding the token ids at each (b,t) position
--     // wte is (V,C) of token embeddings, short for "weight token embeddings"
--     // wpe is (maxT,C) of position embeddings, short for "weight positional embedding"
--     for (int b = 0; b < B; b++) {
--         for (int t = 0; t < T; t++) {
--             // seek to the output position in out[b,t,:]
--             float* out_bt = out + b * T * C + t * C;
--             // get the index of the token at inp[b, t]
--             int ix = inp[b * T + t];
--             // seek to the position in wte corresponding to the token
--             float* wte_ix = wte + ix * C;
--             // seek to the position in wpe corresponding to the position
--             float* wpe_t = wpe + t * C;
--             // add the two vectors and store the result in out[b,t,:]
--             for (int i = 0; i < C; i++) {
--                 out_bt[i] = wte_ix[i] + wpe_t[i];
--             }
--         }
--     }
-- }


def finMaxT_of_finT
  (h: T ≤ maxT)
  (t: Fin T)
: Fin maxT
:=
  -- t < T < maxT
  let h' := Nat.le_trans t.isLt h
  ⟨t.val, h'⟩

def encoder_forward
  (inp: Vector (Fin V) T)
  (wte: Vector (Vector Float C) V)
  (wpe: Vector (Vector Float C) maxT)
  (h: T ≤ maxT)
: Vector (Vector Float C) T
 :=
  inp.mapIdx (λ idx ix => (wte.get ix) + (wpe.get (finMaxT_of_finT h idx)))

def encoder_forward_batch
  (inp: Vector (Vector (Fin V) T) B)
  (wte: Vector (Vector Float C) V)
  (wpe: Vector (Vector Float C) maxT)
  (h: T ≤ maxT)
: Vector (Vector (Vector Float C) T) B
  :=
    inp.map (λ inp => encoder_forward inp wte wpe h)


-- void encoder_backward(float* dwte, float* dwpe,
--                       float* dout, int* inp,
--                       int B, int T, int C) {
--     // Iterate over each batch
--     for (int b = 0; b < B; b++) {
--         // Iterate over each token position
--         for (int t = 0; t < T; t++) {
--             // Calculate the pointer to the current position in dout
--             float* dout_bt = dout + b * T * C + t * C;
--             // Get the token index at the current position
--             int ix = inp[b * T + t];
--             // Calculate the pointer to the corresponding position in dwte
--             float* dwte_ix = dwte + ix * C;
--             // Calculate the pointer to the corresponding position in dwpe
--             float* dwpe_t = dwpe + t * C;
--             // Iterate over each dimension of the embedding
--             for (int i = 0; i < C; i++) {
--                 // Get the gradient at the current position
--                 float d = dout_bt[i];
--                 // Accumulate the gradient for the token embedding
--                 dwte_ix[i] += d;
--                 // Accumulate the gradient for the position embedding
--                 dwpe_t[i] += d;
--             }
--         }
--     }
-- }



def encoder_backward
  (dout: Vector (Vector Float C) T)
  (inp: Vector (Fin V) T)
  (h: T ≤ maxT)
: (Vector (Vector Float C) V) × (Vector (Vector Float C) maxT)
:=
  let dwte_updater := λ
    (dwte: Vector (Vector Float C) V)
    ((d: Vector Float C), (ix: Fin V))
  => dwte.modify ix (λ v => v + d)

  let init_dwte := Vector.replicate V (Vector.replicate C 0)
  let dwte := Vector.foldl dwte_updater init_dwte (Vector.zip dout inp)

  let dwpe_updater := λ
    (dwpe: Vector (Vector Float C) maxT)
    ((t: Fin T),(d: Vector Float C))
  => dwpe.modify (finMaxT_of_finT h t) (λ v => v + d)

  let init_dwpe := .replicate maxT (.replicate C 0)
  let dwpe := Vector.foldl dwpe_updater init_dwpe (Vector.mapIdx Prod.mk dout)

  (dwte, dwpe)

def idk: Char := Id.run do
  for h : i in [:10] do
    return 'a'
  return 'a'

-- accumulate over batches
def encoder_backward_batch
  (dout: Vector (Vector (Vector Float C) T) B)
  (inp: Vector (Vector (Fin V) T) B)
: (Vector (Vector Float C) V) × (Vector (Vector Float C) V)
:=
'
