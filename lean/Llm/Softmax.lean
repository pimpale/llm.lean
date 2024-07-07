import LinearAlgebra.Vector

def softmax(x: Vector Float n) : Vector Float n :=
  let maxv := x.foldl max (-Float.inf)
  let x := x.map (λ xi => xi - maxv)
  let exp_x := x.map Float.exp
  let sum_exp_x := exp_x.sum
  exp_x.map (λ x => x / sum_exp_x)


def softmax_backward
  (dout: Vector Float n)
  (out: Vector Float n)
: Vector Float n :=
  let sum := (dout * out).sum
  let dx := dout - Vector.of sum
  out * dx

#eval softmax !v[1, 2, 3]


#eval softmax !v[5]
