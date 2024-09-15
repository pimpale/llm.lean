import LinearAlgebra.Vector



/-!
  Embedding matrix for language model. Shape vocab_size x embedding_dim
-/
structure Embedding (embedDim:Nat := 3072) (vocabSize:Nat := 30000) where
  matrix : Vector (Vector Float embedDim) vocabSize
  