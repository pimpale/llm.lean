import Lake
open System Lake DSL

package llm.lean where
  srcDir := "lean"
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

lean_lib LinearAlgebra
lean_lib Llm

@[default_target]
lean_exe test where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require aesop from git
  "https://github.com/leanprover-community/aesop.git"
-- v1.4.1 works with toolchain 4.10.0-rc1
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.4.1"
