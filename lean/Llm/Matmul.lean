import LinearAlgebra.Vector


-- #eval Vector.matmul !v[!v[1,2,3],!v[4,5,6]]  !v[!v[7,8],!v[9,10],!v[11,12]]

#check
  let a: Vector 2 (Vector 3 Float) := sorry
  let b: Vector 3 (Vector 2 Float) := sorry
  let c := Vector.matmul a b
  c




def matmul_batched [Add α] [Mul α] [Zero α]
  (a: Vector B (Vector M (Vector P α)))
  (b: Vector B (Vector P (Vector N α)))
: Vector B (Vector M (Vector N α )) :=
  .zipWith (· * ·) a b

/--
  unbatched backward.
  returns dinp, dweight
-/
def matmul_backward
  (inp: Vector P (Vector N Float))
  (weight: Vector M (Vector P Float))
  (dout: Vector M (Vector N Float))
: (Vector P (Vector N Float )) × (Vector M (Vector P Float ))
:=

  let dinp := weight.transpose * dout
  let dweight := dout * inp.transpose

  (dinp, dweight)

/--
  We reduce the weight but not the input.
-/
def matmul_backward_batched
  (inp: Vector B (Vector P (Vector N Float)))
  (weight: Vector B (Vector M (Vector P Float)))
  (dout: Vector B (Vector M (Vector N Float)))
: (Vector B (Vector P (Vector N Float))) × (Vector M (Vector P Float))
:=
  let inp_t := inp.map (·.transpose)
  let weight_t := weight.map (·.transpose)

  let dinp_b := matmul_batched weight_t dout
  let dweight_b := matmul_batched dout inp_t

  let dweight := dweight_b.sum

  (dinp_b, dweight)
