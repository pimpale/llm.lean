import LinearAlgebra.Vector

def finMaxT_of_finT
  (h: T ≤ maxT)
  (t: Fin T)
: Fin maxT
:=
  -- t < T < maxT
  let h' := Nat.le_trans t.isLt h
  ⟨t.val, h'⟩

abbrev Matrix (Rows Cols : Nat) (α : Type) := Vector Rows (Vector Cols α)

def good (input : Float) : Float := sorry

def matMul
  (m1: Matrix R1 C1 α)
  (m2: Matrix C1 C2 α)
: Matrix R1 C2 α
:=
  m1.map (λ row => m2.map (λ col => row.zip col))


def encoder_forward
  (inp: Vector T (Fin V))
  (wte: Vector V (Vector C Float))
  (wpe: Vector maxT (Vector C Float))
  (h: T ≤ maxT)
: Vector T (Vector C Float) :=
  inp.mapIdx (λ idx ix => (wte.get ix) + (wpe.get (finMaxT_of_finT h idx)))

def encoder_forward_batch
  (inp: Vector B (Vector T (Fin V)))
  (wte: Vector V (Vector C Float))
  (wpe: Vector maxT (Vector C Float))
  (h: T ≤ maxT)
: Vector B (Vector T (Vector C Float)) :=
  inp.map (λ inp => encoder_forward inp wte wpe h)

def encoder_backward
  (dout: Vector T (Vector C Float))
  (inp: Vector T (Fin V))
  (h: T ≤ maxT)
: Vector V (Vector C Float) × Vector maxT (Vector C Float) :=

  let dwte_updater := fun
    (dwte : Vector V (Vector C Float))
    ((d : Vector C Float), (ix : Fin V))
  => dwte.modify ix (· + d)

  let dwpe_updater := fun
    (dwpe : Vector maxT (Vector C Float))
    ((t : Fin T), (d : Vector C Float))
  => dwpe.modify (finMaxT_of_finT h t) (· + d)

  let dwte := (dout.zip inp).foldl dwte_updater (init := 0)

  let dwpe := (dout.mapIdx (·, ·)).foldl dwpe_updater (init := 0)

  (dwte, dwpe)


/--
  out: C-dimensional vector summarizing token & position
  inp: (B,T) of integers, holding the token ids at each (b,t) position
  wte: (V,C) of token embeddings, short for "weight token embeddings"
  wpe is (maxT,C) of position embeddings, short for "weight positional embedding"
--/
def encoder_backward_batch
  (dout_b: Vector B (Vector T (Vector C Float)))
  (inp_b: Vector B (Vector T (Fin V)))
  (h: T ≤ maxT)
  -- gradient is accumulated, so no batch dim in output `dwte` or `dwpe`
: Vector V (Vector C Float) ×  Vector maxT (Vector C Float)
:=
  let all_data :=
    (dout_b.zip inp_b).map (fun (dout, inp) => encoder_backward dout inp h)
  let (dwte_b, dwpe_b) := (all_data.map Prod.fst, all_data.map Prod.snd)
  -- accumulate over batches
  let (dwte, dwpe) := (dwte_b.sum, dwpe_b.sum)

  (dwte, dwpe)
