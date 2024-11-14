import LinearAlgebra.Vector
import Llm.FiniteDiff



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
  a.zipWith (· * ·) b

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



open Vector in
/-- Test for matmul_backward using finite difference-/
def test_matmul_backward (N M P : Nat) : Bool := Id.run do
  let (ε, ATOL) : Float × Float := (1e-4, 1e-3)
  /- Generate input matrices -/
  let inp : Vector P (Vector N Float) := Vector.replicate P (Vector.replicate N 1.0)
  let weight : Vector M (Vector P Float) := Vector.replicate M (Vector.replicate P 2.0)
  let dout : Vector M (Vector N Float) := Vector.replicate M (Vector.replicate N 3.0)

  /- Compute analytical gradients -/
  let (dinp, dweight) : Vector P (Vector N Float) × Vector M (Vector P Float) := matmul_backward inp weight dout

  /- Initialize variables for maximum differences -/
  let mut max_diff_inp := 0.0
  let mut max_diff_weight := 0.0

  let (col_range, row_range, weight_range) := (allFins P, allFins N, allFins M)

  for p in col_range do
    for n in row_range do

      let inp_perturbed : Vector P (Vector N Float) := inp.modify p (fun row ↦ row.modify n (fun _ ↦ inp[p][n] + ε))
      let out : Vector M (Vector N Float) := weight * inp
      let out_perturbed : Vector M (Vector N Float) := weight * inp_perturbed
      let loss_diff := ((out_perturbed - out).sum ⬝ᵥ dout.sum)
      let numerical_gradient := loss_diff / ε
      let analytical_gradient := dinp[p][n]
      let diff := (analytical_gradient - numerical_gradient).abs
      if diff > max_diff_inp then
        max_diff_inp := diff

  /- Compute numerical gradients for weight -/

  for m in weight_range do
    for p in col_range do
      let weight_perturbed := weight.modify m (fun row ↦ row.modify p (fun _ ↦ weight[m][p] + ε))
      let out : Vector M (Vector N Float) := weight * inp
      let out_perturbed := weight_perturbed * inp
      let loss_diff := ((out_perturbed - out).sum ⬝ᵥ dout.sum)
      let numerical_gradient := loss_diff / ε
      let analytical_gradient := dweight[m][p]
      let diff := (analytical_gradient - numerical_gradient).abs
      if diff > max_diff_weight then
        max_diff_weight := diff

  /- Check if the maximum differences are within tolerance -/
  return (max_diff_inp < ATOL) && (max_diff_weight < ATOL)
