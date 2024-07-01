
import LinearAlgebra.Vector
-- void layernorm_forward(float* out, float* mean, float* rstd,
--                        float* inp, float* weight, float* bias,
--                        int B, int T, int C) {
--     // reference: https://pytorch.org/docs/stable/generated/torch.nn.LayerNorm.html
--     // both inp and out are (B,T,C) of the activations
--     // mean and rstd are (B,T) buffers, to be used later in backward pass
--     // at each position (b,t) of the input, the C-dimensional vector
--     // of activations gets normalized, then scaled and shifted
--     float eps = 1e-5f;
--     for (int b = 0; b < B; b++) {
--         for (int t = 0; t < T; t++) {
--             // seek to the input position inp[b,t,:]
--             float* x = inp + b * T * C + t * C;
--             // calculate the mean
--             float m = 0.0f;
--             for (int i = 0; i < C; i++) {
--                 m += x[i];
--             }
--             m = m/C;
--             // calculate the variance (without any bias correction)
--             float v = 0.0f;
--             for (int i = 0; i < C; i++) {
--                 float xshift = x[i] - m;
--                 v += xshift * xshift;
--             }
--             v = v/C;
--             // calculate the rstd (reciprocal standard deviation)
--             float s = 1.0f / sqrtf(v + eps);
--             // seek to the output position in out[b,t,:]
--             float* out_bt = out + b * T * C + t * C;
--             for (int i = 0; i < C; i++) {
--                 float n = (s * (x[i] - m)); // normalize
--                 float o = n * weight[i] + bias[i]; // scale and shift
--                 out_bt[i] = o; // write
--             }
--             // cache the mean and rstd for the backward pass later
--             mean[b * T + t] = m;
--             rstd[b * T + t] = s;
--         }
--     }
-- }



def eps := 1e-5

def layernorm_forward
  (inp: Vector Float C)
  (weight: Vector Float C)
  (bias: Vector Float C)
: Float × Float × (Vector Float C)
  :=
  -- calculate the mean
  let mean := (inp.foldl (λ m x => m + x) 0.0) / C.toFloat;
  -- calculate the variance (without any bias correction)
  let variance := (inp.foldl (λ v x => v + (x - mean) * (x - mean)) 0) / C.toFloat;
  -- calculate the rstd (reciprocal standard deviation)
  let rstd := 1 / (variance + eps).sqrt;
  -- normalize, scale, and shift
  let out := inp.mapIdx (λ i x => (rstd * (x - mean)) * weight.get i + bias.get i);

  (mean, rstd, out)

def layernorm_forward_batch
  (inp: Vector (Vector (Vector Float C) T) B)
  (weight: Vector Float C)
  (bias: Vector Float C)
: ((Vector (Vector Float T) B) × (Vector (Vector Float T) B) ×   (Vector (Vector (Vector Float C) T) B))
  :=
    let all_data := inp.map (λ inp => inp.map (λ inp => layernorm_forward inp weight bias))

    let mean := all_data.map (λ row => row.map (λ (m, _, _) => m));
    let rstd := all_data.map (λ row => row.map (λ (_, s, _) => s));
    let out := all_data.map (λ row => row.map (λ (_, _, o) => o));

    (mean, rstd, out)


def layernorm_backward
  (dout: Vector Float C)
  (inp: Vector Float C)
  (mean: Float)
  (rstd: Float)
  (weight: Vector Float C)
