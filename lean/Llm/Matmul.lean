import LinearAlgebra.Vector


#eval Vector.matmul !v[!v[1,2,3],!v[4,5,6]]  !v[!v[7,8],!v[9,10],!v[11,12]]
-- a: B x T x C
-- b: B x C x OC
-- out: B x T x OC
def matmul_batched [Add α] [Mul α] [Zero α] (a: Vector (Vector (Vector α P) M) B) (b: Vector (Vector (Vector α N) P) B) : Vector (Vector (Vector α N) M) B :=
  .zipWith (· * ·) a b

def _root_.Std.Range.foldr (r: Std.Range) (f: Nat -> b -> b) (init: b) : b := Id.run do
  let mut acc := init
  for i in r do
    acc := f i acc
  acc

def _root_.Std.Range.foldl (r: Std.Range) (f: b -> Nat -> b) (init: b) : b := Id.run do
  let mut acc := init
  for i in r do
    acc := f acc i
  acc

#eval [0:5].foldr (λ i acc => acc + i) 0
#eval [0:5].foldl (λ acc i => acc + i) 0

/--
  unbatched backward.
  returns dinp, dweight
-/
def matmul_backward
  (inp: Vector (Vector Float N) P)
  (weight: Vector (Vector Float P) M)
  (dout: Vector (Vector Float N) M)
: (Vector (Vector Float N) P) × (Vector (Vector Float P) M)
:=

  let dinp := weight.transpose * dout
  let dweight := dout * inp.transpose

  (dinp, dweight)

/--
  We reduce the weight but not the input.
-/
def matmul_backward_batched
  (inp: Vector (Vector (Vector Float N) P) B)
  (weight: Vector (Vector (Vector Float P) M) B)
  (dout: Vector (Vector (Vector Float N) M) B)
: (Vector (Vector (Vector Float N) P) B) × (Vector (Vector Float P) M)
:=
  let inp_t := inp.map (·.transpose)
  let weight_t := weight.map (·.transpose)

  let dinp_b := matmul_batched weight_t dout
  let dweight_b := matmul_batched dout inp_t

  let dweight := dweight_b.sum

  (dinp_b, dweight)
