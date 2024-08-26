-- @dataclass
-- class MultiHeadAttentionConfig:
--     # Number of attention heads
--     n_heads: int
--     # Dimension of the output vector
--     d_out: int
--     # Dimension of the embedding of each token
--     d_embed: int
--     # Dimension of the key, query and value vectors
--     d_k: int
--     # Size of the input sequence
--     ctx_len: int

-- class MultiHeadAttention(nn.Module):
--     def __init__(self, config: MultiHeadAttentionConfig):
--         super().__init__()
--         self.config = config
--         self.heads = nn.ModuleList([
--             AttentionHead(AttentionHeadConfig(
--                 d_embed=config.d_embed,
--                 d_k=config.d_k,
--                 ctx_len=config.ctx_len
--             )) for _ in range(config.n_heads)
--         ])
--         self.o = nn.Linear(config.n_heads*config.d_k, config.d_out, bias=False)

--     def forward(self, x):
--         return self.o(torch.cat([head(x) for head in self.heads], dim=-1))

import Llm.Dense
import Llm.Attention

structure MultiHeadAttentionConfig where
  /-- Number of attention heads -/
  n_heads: Nat
  /-- Dimension of the output vector -/
  d_out: Nat
  /-- Dimension of the embedding of each token -/
  d_embed: Nat
  /-- Dimension of the key, query and value vectors -/
  d_k: Nat
  /-- Size of the input sequence -/
  ctx_len: Nat

structure MultiHeadAttention where
  config: MultiHeadAttentionConfig
  heads: Vector AttentionHead config.n_heads
  o: Dense (config.n_heads * config.d_k) config.d_out

def MultiHeadAttention.mk' (config: MultiHeadAttentionConfig) MultiHeadAttention := do
  let mut heads := Vector.empty
  for _ in [0:config.n_heads] do
    let head :=  {
      d_embed := config.d_embed,
      d_k := config.d_k,
      ctx_len := config.ctx_len
    }
    heads := heads.push head
  let o := Dense.mk (config.n_heads * config.d_k) config.d_out
  pure { config := config, heads := heads, o := o }

def MultiHeadAttention.forward (self: MultiHeadAttention) (x: Vector (Vector Float self.config.d_embed) self.config.ctx_len) : Vector (Vector Float self.config.d_out) self.config.ctx_len :=
  let headOutputs := self.heads.map (fun head => head.forward x)
  let concatenated := Vector.concat headOutputs
  self.o.forward concatenated

def mha (n_heads: Nat := 8) (d_out d_embed d_k ctx_len: Nat) : IO MultiHeadAttention := do
  MultiHeadAttention.mk {
    n_heads := n_heads,
    d_out := d_out,
    d_embed := d_embed,
    d_k := d_k,
    ctx_len := ctx_len
  }
