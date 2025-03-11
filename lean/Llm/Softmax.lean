import Llm.FiniteDiff
import Llm.Matmul
import Batteries.Lean.Float

def softmax(x: Vector Float n) : Vector Float n :=
  let maxv := x.foldl max (-Float.inf)
  let x := x.map (· - maxv)
  let exp_x := x.map Float.exp
  let sum_exp_x := exp_x.sum
  exp_x.map (· / sum_exp_x)

def softmax_backward
  (dout: Vector Float n)
  (out: Vector Float n )
: Vector Float n  :=
  -- -- Compute Jacobian matrix
  let S : Vector (Vector Float n) n  := .ofFn fun r => .ofFn fun c =>
      if r == c
      then out[r] * (1 - out[c])
      else -out[r] * out[c]

  -- Multiply Jacobian with incoming gradient
  let dout_m := (Vector.singleton dout)

  -- compute vector jacobian product (vT * J)
  let vjp := matmul dout_m S

  -- return the result (as vector)
  vjp[0]

#eval finiteDiff softmax #v[1, 2, 3]

#eval softmax #v[1, 2, 3]

#eval softmax_backward #v[1,2,3] (softmax #v[1,2,3])
