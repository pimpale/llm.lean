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


def matmul {α : Type u} [Add α] [Mul α] [Zero α] {R C I: Nat} (a: Vector (Vector α I) R) (b: Vector (Vector α C) I) : Vector (Vector α C) R :=  Id.run do
  let rows := a
  let cols := b.transpose

  Vector.ofFn (fun r =>
    Vector.ofFn (fun c =>
      rows[r].dot cols[c]
    )
  )

def matmul_batched {α : Type u} [Add α] [Mul α] [Zero α] {B T C OC: Nat} (a: Vector (Vector (Vector α C) T) B) (b: Vector (Vector (Vector α C) OC) B) : Vector (Vector (Vector α OC) T) B := Id.run do
  -- TODO i miss reshape already
  let batched_transpose_b := b.map (·.transpose)
  a.zip batched_transpose_b |>.map (λ (a, b) => matmul a b)


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

/-- unbatched backward. -/
def matmul_backward
  {T C OC: Nat}
  (dinp: Vector (Vector Float C) T)
  (dweight: Vector (Vector Float C) OC)
  (weight: Vector (Vector Float C) OC)
  (dout: Vector (Vector Float OC) T)
  (inp: Vector (Vector Float C) T)
: (Vector (Vector Float C) T) × (Vector (Vector Float C) OC)
:=

  -- Backward into inp
  let dinp' := dinp.mapIdx (λ t col =>
    col.mapIdx (λ i _ =>
      ([0:OC]).foldl (λ acc o =>
        acc + (weight[o]'sorry)[i]'sorry * dout[t][o]'sorry
      ) 0
    )
  )

  -- Backward into weight
  let dweight' := dweight.mapIdx (λ o row =>
    row.mapIdx (λ i _ =>
      ([0:T]).foldl (λ acc t =>
        acc + (inp[t]'sorry)[i]'sorry * (dout[t]'sorry)[o]'sorry
      ) 0
    )
  )

  (dinp', dweight')
