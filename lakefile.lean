import Lake
open System Lake DSL

package llm.lean where
  srcDir := "lean"
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

lean_lib LinearAlgebra
lean_lib Llm

@[default_target]
lean_exe test where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require scilean from git "https://github.com/lecopivo/scilean.git" @ "92b1246"
