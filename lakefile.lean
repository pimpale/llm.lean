import Lake
open System Lake DSL

package llm.lean where
  srcDir := "lean"

lean_lib LinearAlgebra
lean_lib Llm

@[default_target]
lean_exe test where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require scilean from git "https://github.com/lecopivo/scilean.git" @ "1de5c61aba75b496962ba9eb991570bb21169516"
require plausible from git "https://github.com/leanprover-community/plausible.git"
require "leanprover-community" / "batteries" @ git "main"
