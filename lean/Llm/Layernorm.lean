import LinearAlgebra.Vector
import Llm.FiniteDiff

def layernorm
  (inp: Vector Float C)
  (weight: Vector Float C)
  (bias: Vector Float C)
  (ε : Float := 1e-5)
: Float × Float × (Vector Float C)
  :=
  -- calculate the mean
  let meanVal := inp.mean
  -- calculate the variance (without any bias correction)
  let xshift := inp - Vector.replicate C meanVal
  let variance := (xshift ⊙ xshift).mean
  -- calculate the rstd (reciprocal standard deviation)
  let rstd := 1 / (variance + ε).sqrt
  -- normalize, scale, and shift
  let out := inp.mapIdx (λ c x => (rstd * (x - meanVal)) * weight[c] + bias[c])

  (meanVal, rstd, out)

def layernorm_batched
  (inp: Vector (Vector (Vector Float C) T) B)
  (weight: Vector Float C)
  (bias: Vector Float C)
  -- mean, rstd, out
: ((Vector (Vector Float T) B) × (Vector (Vector Float T) B) ×   (Vector (Vector (Vector Float C) T) B))
  :=
    let all_data := inp.map (·.map (layernorm · weight bias))

    let mean := all_data.map (·.map (λ (m, _, _) => m))
    let rstd := all_data.map (·.map (λ (_, s, _) => s))
    let out := all_data.map (·.map (λ (_, _, o) => o))

    (mean, rstd, out)

def layernorm_backward
  (dout: Vector Float C)
  (inp: Vector Float C)
  (mean: Float)
  (rstd: Float)
  (weight: Vector Float C)
-- dx, dw, db
: (Vector Float C) × (Vector Float C) × (Vector Float C)
  :=
  -- recomputing the norm
  let norm' := (inp - Vector.replicate C mean) ⊙ (Vector.replicate C rstd)
  -- gradients for weights, bias
  let db := dout
  let dw :=  dout ⊙ norm'
  -- gradients for input
  let dnorm := dout ⊙ weight
  let dnorm_mean := Vector.replicate C (dnorm.mean)
  let dnorm_norm_mean := Vector.replicate C ((dnorm ⊙ norm').mean)
  let dx := dnorm - dnorm_mean - (norm' ⊙ dnorm_norm_mean)
  let dx := dx ⊙ (Vector.replicate C rstd)

  (dx, dw, db)

def layernorm_backward_batch
  (dout: Vector (Vector (Vector Float C) T) B)
  (inp: Vector (Vector (Vector Float C) T) B)
  (mean: Vector (Vector Float T) B)
  (rstd: Vector (Vector Float T) B)
  (weight: Vector Float C)
  -- dx, dw, db
: (Vector (Vector (Vector Float C) T) B) × (Vector (Vector Float C) B) × (Vector (Vector Float C) B)
  :=
  let all_data := Vector.ofFn (fun b => Vector.ofFn (fun t => layernorm_backward dout[b][t] inp[b][t] mean[b][t] rstd[b][t] weight))

  let dx := all_data.map (·.map (fun (dx, _, _) => dx))
  let dw := all_data.map (·.map (fun (_, dw, _) => dw) |>.sum)
  let db := all_data.map (·.map (fun (_, _, db) => db) |>.sum)

  (dx, dw, db)


def test_layernorm_backward_finiteDiff (ε : Float := 1e-4) (tolerance : Float := 1e-3) : IO Unit := do

  let inp := !v[1.0, 2.0, 3.0, 4.0]
  let weight := !v[0.1, 0.2, 0.3, 0.4]
  let bias := !v[0.01, 0.02, 0.03, 0.04]
  let dout := !v[0.1, 0.2, 0.3, 0.4]

  let (mean, rstd, out) := layernorm inp weight bias
  let (dx, dw, db) := layernorm_backward dout inp mean rstd weight
  IO.println s!"{dx}, {dw}, {db}"

#eval test_layernorm_backward_finiteDiff
