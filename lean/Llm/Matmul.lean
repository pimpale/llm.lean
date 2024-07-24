import LinearAlgebra.Vector

-- void matmul_backward(float* dinp, float* dweight, float* dbias,
--                      const float* dout, const float* inp, const float* weight,
--                      int B, int T, int C, int OC) {
--     // most of the running time is spent here and in matmul_forward
--     // this backward could be done in a single "round" of loops
--     // but that doesn't afford an efficient parallelization strategy

--     // backward into inp first, parallelize over B,T
--     #pragma omp parallel for collapse(2)
--     for (int b = 0; b < B; b++) {
--         for (int t = 0; t < T; t++) {
--             const float* dout_bt = dout + b * T * OC + t * OC;
--             float* dinp_bt = dinp + b * T * C + t * C;
--             for (int o = 0; o < OC; o++) {
--                 const float* wrow = weight + o*C;
--                 float d = dout_bt[o];
--                 for (int i = 0; i < C; i++) {
--                     dinp_bt[i] += wrow[i] * d;
--                 }
--             }
--         }
--     }
--     // backward into weight/bias, parallelize over output channels OC
--     #pragma omp parallel for
--     for (int o = 0; o < OC; o++) {
--         for (int b = 0; b < B; b++) {
--             for (int t = 0; t < T; t++) {
--                 const float* dout_bt = dout + b * T * OC + t * OC;
--                 const float* inp_bt = inp + b * T * C + t * C;
--                 float* dwrow = dweight + o*C;
--                 float d = dout_bt[o];
--                 if (dbias != NULL) { dbias[o] += d; }
--                 for (int i = 0; i < C; i++) {
--                     dwrow[i] += inp_bt[i] * d;
--                 }
--             }
--         }
--     }
-- }


def matmul [Add α] [Mul α] [Zero α] (a: Vector (Vector α I) R) (b: Vector (Vector α C) I) : Vector (Vector α C) R :=
  let rows := a
  let cols := b.transpose

  .ofFn fun r =>
    .ofFn fun c =>
      rows[r].dot cols[c]

/--Matrix multiplication.-/
instance [Add α] [Mul α] [Zero α] : HMul (Vector (Vector α I) R) (Vector (Vector α C) I) (Vector (Vector α C) R) where
  hMul := matmul

#eval matmul !v[!v[1,2,3],!v[4,5,6]] !v[!v[7,8],!v[9,10],!v[11,12]]
-- a: B x T x C
-- b: B x C x OC
-- out: B x T x OC
def matmul_batched [Add α] [Mul α] [Zero α] (a: Vector (Vector (Vector α P) M) B) (b: Vector (Vector (Vector α N) P) B) : Vector (Vector (Vector α N) M) B :=
  .zipWith matmul a b

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
  (inp: Vector (Vector Float N) P)
  (weight: Vector (Vector Float P) M)
  (dout: Vector (Vector Float N) M)
: (Vector (Vector Float N) P) × (Vector (Vector Float P) M)
:=
  -- first define transposes
  let inp_t := inp.transpose
  let weight_t := weight.transpose

  let dinp := matmul weight_t dout
  let dweight := matmul dout inp_t

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
  let inp_t := inp.map (λ x => x.transpose)
  let weight_t := weight.map (λ x => x.transpose)

  let dinp_b := matmul_batched weight_t dout
  let dweight_b := matmul_batched dout inp_t

  let dweight := dweight_b.foldl (·+·) 0

  (dinp_b, dweight)
