import Lake
open System Lake DSL

package llm.lean where
  srcDir := "lean"

lean_lib LinearAlgebra
lean_lib Llm

@[default_target]
lean_exe test where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
