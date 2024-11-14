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



import Llm.Dense
import Llm.AttentionHead

structure MultiHeadAttention (H Dₖ D_emb D_out: ℕ) where
  heads: Vector H (AttentionHead Dₖ D_emb)
  o: Dense (H * Dₖ) D_out

def MultiHeadAttention.forward
  (self: MultiHeadAttention H Dₖ D_emb D_out)
  (x: Vector T (Vector D_emb Float))
: Vector T (Vector D_out Float)
:=
  let headOutputs := self.heads.map (fun head => (head.forward x).transpose)
  let concatenated := headOutputs.stack.transpose
  self.o.forward concatenated

def MultiHeadAttention.forward_batched
  (self: MultiHeadAttention H Dₖ D_emb D_out)
  (x: Vector B (Vector T (Vector D_emb Float)))
: Vector B (Vector T (Vector D_out Float))
:=
  x.map self.forward



def MultiHeadAttention.backward
  (self: MultiHeadAttention H Dₖ D_emb D_out)
  (x: Vector T (Vector D_emb Float))
  (dout: Vector T (Vector D_out Float))
: MultiHeadAttention H Dₖ D_emb D_out × (Vector T (Vector D_emb Float))
:=
  let headOutputs := self.heads.map (fun head => (head.forward x).transpose)
  let concatenated := headOutputs.stack.transpose
  let (d_o, dconcatenated) := self.o.backward concatenated dout
  let headBackwards := dconcatenated.split
  let headBackwards' := headBackwards.map (·.transpose)
  let (heads, dinp) := (self.heads, headBackwards').map (·.backward x)
  (MultiHeadAttention.mk heads d_o, dinp)
-- TODO name this unapologetic when we're done and sorry free
