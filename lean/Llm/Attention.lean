import LinearAlgebra.Vector
import Llm.Matmul
import Llm.Softmax

-- def forward(self, x):
--     # x in (batch_size, ctx_len, d_embed)
--     # q in (batch_size, ctx_len, d_k)
--     q = self.q(x)
--     # k in (batch_size, ctx_len, d_k)
--     k = self.k(x)

--     # masked self attention
--     # a in (batch_size, ctx_len, ctx_len)
--     a = (q @ k.transpose(-2, -1)) / (self.config.d_k ** 0.5)
--     a = a.masked_fill(self.mask == 0, float("-inf"))
--     a = F.softmax(a, dim=-1)

--     # v in (batch_size, ctx_len, d_k)
--     v = self.v(x)

--     # att in (batch_size, ctx_len, d_k)
--     att = a @ v
--     return att


def tril [Zero α] (triangle_value: α) : Vector (Vector α n) n :=
  Vector.ofFn (fun i =>
    Vector.ofFn (fun j =>
      if j < i then triangle_value else 0
    )
  )

def attention_forward
  (q: Vector (Vector Float D_K) T)
  (k: Vector (Vector Float D_K) T)
  (v: Vector (Vector Float D_K) T)
: Vector (Vector Float D_K) T :=
  let k_t := k.transpose
  let a := matmul q k_t
  let norm_factor :=  (Float.ofNat D_K).sqrt
  let a1 := a.map (λ x => x.map (λ y => y / norm_factor))
  let a2 := a1 + tril (-Float.inf)
  let a3 := a2.map softmax

  matmul a3 v

def attention_backwards
  (dout: Vector (Vector Float D_K) T)
  (q: Vector (Vector Float D_K) T)
  (k: Vector (Vector Float D_K) T)
  (v: Vector (Vector Float D_K) T)
-- dq, dk, dv
: (Vector (Vector Float D_K) T) × (Vector (Vector Float D_K) T) × (Vector (Vector Float D_K) T) :=
  let k_t := k.transpose
  let a := matmul q k_t
  let norm_factor :=  (Float.ofNat D_K).sqrt
  let a1 := a.map (λ x => x.map (λ y => y / norm_factor))
  let a2 := a1 + tril (-Float.inf)
  let a3 := a2.map softmax

  let out := matmul a3 v


  let dv := matmul a3.transpose dout
  let da3 := matmul dout v.transpose

  let da2 := da3.map (λ x => x * (1 - x))

  sorry
