
-- #eval Vector.matmul !v[!v[1,2,3],!v[4,5,6]]  !v[!v[7,8],!v[9,10],!v[11,12]]

import Llm.FloatTensor

def dot [Add α] [Mul α] [Zero α]
  (a: Vector α N)
  (b: Vector α N)
: α :=
  (a.zipWith (· * ·) b).sum

def matmul [Add α] [Mul α] [Zero α]
  (a: Vector (Vector α P) M)
  (b: Vector (Vector α N) P)
: Vector (Vector α N) M :=
  let b_t := transpose b
  Vector.ofFn (fun i =>
    Vector.ofFn (fun j => dot a[i] b_t[j])
  )

#check
  let a: Vector (Vector Float 3) 2 := sorry
  let b: Vector (Vector Float 2) 3 := sorry
  let c := matmul a b
  c


def matmul_batched [Add α] [Mul α] [Zero α]
  (a: Vector (Vector (Vector α P) M) B)
  (b: Vector (Vector (Vector α N) P) B)
: Vector (Vector (Vector α N) M) B :=
  .zipWith matmul a b

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
  let dinp := matmul (transpose weight) dout
  let dweight := matmul dout (transpose inp)

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
  let inp_t := inp.map transpose
  let weight_t := weight.map transpose

  let dinp_b := matmul_batched weight_t dout
  let dweight_b := matmul_batched dout inp_t

  let dweight :=  dweight_b.sum

  (dinp_b, dweight)
