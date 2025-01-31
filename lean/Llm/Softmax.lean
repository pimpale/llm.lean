import LinearAlgebra.Vector
import Llm.FiniteDiff
import SciLean
-- import SciLean.Modules.ML.XLA.TensorIndex
import Lean

open Lean Elab Command

macro "#[" pat:term "←" arr:term "|" pred:term "]" : term => `(Array.filter (fun $pat => $pred) $arr)

-- Usage
#eval #[x ← #[1, 2, 3, 4, 5] | x % 2 == 0]
-- Result: #[2, 4]


def SciLean.DataArrayN.sum {n: Nat} (x: Float^[n]) : Float := x.foldl (init := 0.0) (· + ·)

/-- Positive Infinity (∞) in Float -/
def Float.inf : Float := 1.0 / 0.0
/-- Negative Infinity (-∞) in Float -/
def Float.negInf : Float := -1.0 / 0.0

def softmax(x: Vector n Float) : Vector n Float :=
  let maxv := x.foldl max (init := Float.negInf)
  let x := x.map (· - maxv)
  let exp_x := x.map Float.exp
  let sum_exp_x := exp_x.sum
  exp_x.map (· / sum_exp_x)


def softmax' (x: Float^[n]) : Float^[n] :=
  let maxv := x.foldl max (init := Float.negInf)
  let x := x.mapMono (· - maxv)
  let exp_x := x.mapMono Float.exp
  let sum_exp_x := exp_x.sum
  exp_x.mapMono (· / sum_exp_x)


variable [SciLean.IndexType R] [SciLean.IndexType C] [SciLean.PlainDataType α] [SciLean.PlainDataType β] [SciLean.PlainDataType γ]

/-- Matrix multiplication `A * v` -/
instance [HMul α β γ] [Add γ] [Zero γ]: HMul (α^[R, C]) (β^[C]) (γ^[R]) where
  hMul A v := ⊞ r => ∑ c, A[r,c] * v.get c


/-- Matrix multiplication `v * A` -/
instance [HMul β α γ] [Add γ] [Zero γ]: HMul (β^[R]) (α^[R, C]) (γ^[C]) where
  hMul v A := ⊞ c => ∑ r, v.get r * A[r,c]


-- #eval  ⊞[1.0,2.0,3.0].reshape [3,1]
#eval (⊞[1.0,2.0; 0.0,3.0]: Float^[2,2]) * (⊞[1,1]: Float^[2])
-- def matMul {R C : Nat} (A : Float^[R,C]) (x : Float^[C]) : Float^[R] :=
--   ⊞ i => ∑ j, A[i,j] * x[j]

def softmax_backward'
  (dout out: Float^[n])
: Float^[n] :=
  let S : Float^[n,n] := ⊞ r c => if r == c then out[r] * (1 - out[c]) else -out[r] * out[c]
  dout * S

set_option diagnostics true in
#eval softmax_backward' (⊞[1,2,3]) (softmax' (⊞[1,2,3]))

def softmax_backward
  (dout: Vector n Float)
  (out: Vector n Float )
: Vector n Float  :=
  -- -- Compute Jacobian matrix
  let S : Vector n (Vector n Float) := .ofFn fun r => .ofFn fun c =>
      if r == c
      then out[r] * (1 - out[c])
      else -out[r] * out[c]

  -- Multiply Jacobian with incoming gradient
  let dout_m := (Vector.singleton dout)

  -- compute vector jacobian product (vT * J)
  let vjp := dout_m.matmul S

  -- return the result (as vector)
  vjp[0]

#eval finiteDiff softmax !v[1, 2, 3]

#eval softmax !v[1, 2, 3]

#eval softmax_backward !v[1,2,3] (softmax !v[1,2,3])
