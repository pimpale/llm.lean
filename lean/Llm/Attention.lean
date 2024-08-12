import LinearAlgebra.Vector
import Llm.Matmul
import Llm.Softmax

def tril [Zero α] (triangle_value: α) : Vector (Vector α n) n :=
  Vector.ofFn (fun i =>
    Vector.ofFn (fun j =>
      if j < i then triangle_value else 0
    )
  )

def attention_forward
  (q: Vector (Vector Float Dₖ) T)
  (k: Vector (Vector Float Dₖ) T)
  (v: Vector (Vector Float Dₖ) T)
: Vector (Vector Float Dₖ) T :=
  let a := q * k.transpose
  let norm_factor :=  (Float.ofNat Dₖ).sqrt
  let a1 := a.map (λ x => x.map (λ y => y / norm_factor))
  let a2 := a1 + tril (-Float.inf)
  let a3 := a2.map softmax

  a3 * v

def attention_backwards
  (dout: Vector (Vector Float Dₖ) T)
  (q: Vector (Vector Float Dₖ) T)
  (k: Vector (Vector Float Dₖ) T)
  (v: Vector (Vector Float Dₖ) T)
-- dq, dk, dv
: (Vector (Vector Float Dₖ) T) × (Vector (Vector Float Dₖ) T) × (Vector (Vector Float Dₖ) T) :=
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

  let dq := da * q
  let dk := da * k

  (dq, dk, dv)



-- MHA, transformerblock, layernorm
