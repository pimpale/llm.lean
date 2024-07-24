import LinearAlgebra.Vector

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
: Vector (Vector Float C) T :=
  inp.mapIdx (λ idx ix => (wte.get ix) + (wpe.get (finMaxT_of_finT h idx)))

def encoder_forward_batch
  (inp: Vector (Vector (Fin V) T) B)
  (wte: Vector (Vector Float C) V)
  (wpe: Vector (Vector Float C) maxT)
  (h: T ≤ maxT)
: Vector (Vector (Vector Float C) T) B
  :=
    inp.map (λ inp => encoder_forward inp wte wpe h)

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

  let init_dwpe := .replicate maxT (.replicate C 0.0)
  let dwpe := Vector.foldl dwpe_updater init_dwpe (Vector.mapIdx Prod.mk dout)

  (dwte, dwpe)

/--
-- out: C-dimensional vector summarizing token & position
-- inp: (B,T) of integers, holding the token ids at each (b,t) position
-- wte: (V,C) of token embeddings, short for "weight token embeddings"
-- wpe is (maxT,C) of position embeddings, short for "weight positional embedding"

-- accumulate over batches -/
def encoder_backward_batch
  (dout_b: Vector (Vector (Vector Float C) T) B)
  (inp_b: Vector (Vector (Fin V) T) B)
  (h: T ≤ maxT)
  -- gradient is accumulated, so no batch dim in output `dwte` or `dwpe`
: Vector (Vector Float C) V × Vector (Vector Float C) maxT
:=
  let all_data :=
    (dout_b.zip inp_b).map (λ (dout_b, inp_b) => encoder_backward dout_b inp_b h)
  let (dwte_b, dwpe_b) := (all_data.map Prod.fst, all_data.map Prod.snd)
  let (dwte, dwpe) := (dwte_b.foldl Vector.add Vector.zero, dwpe_b.foldl Vector.add Vector.zero)

  (dwte, dwpe)
