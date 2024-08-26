import LinearAlgebra.Vector
import Llm.Matmul
import Llm.Softmax

def tril [Zero α] (fillValue: α) : Vector C (Vector R α)  :=
  Vector.ofFn (fun c =>
    Vector.ofFn (fun r =>
      -- no ≤ to avoid diagonal. this should take an axis argument.
      if r.val < c.val then fillValue else 0
    )
  )

def attention_forward
  (q k v : Vector T (Vector Dₖ Float))
: Vector T (Vector Dₖ Float) :=
  let a := q * k.transpose
  let norm_factor :=  (Float.ofNat Dₖ).sqrt
  let a1 := a.map (λ x => x.map (λ y => y / norm_factor))
  let a2 := a1 + tril (-Float.inf)
  let a3 := a2.map softmax

  a3 * v

def attention_backwards
  (dout q k v: Vector T (Vector Dₖ Float))
-- dq, dk, dv
: (Vector T (Vector  Dₖ Float)) × (Vector T (Vector  Dₖ Float) ) × (Vector T (Vector  Dₖ Float) ) :=
  let a := q * k.transpose
  let norm_factor :=  1 / (Float.ofNat Dₖ).sqrt
  let a1 := a.map (λ x => x.map (λ y => y * norm_factor))
  let a2 := a1 + tril (-Float.inf)
  let a3 := a2.map softmax

  let dv := a3.transpose * dout
  let da3 := dout * v.transpose
  -- let da2 := da3 -- derivative of sum where one term (the tril) is constant doesn't change derivative
  let da1 := Vector.zipWith softmax_backward da3 a3

  let da := da1.map (λ x => x.map (λ y => y * norm_factor))

  let (dq, dk) := (da * q, da * k)

  (dq, dk, dv)



-- MHA, transformerblock, layernorm
