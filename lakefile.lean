import Lake
open Lake DSL

package «llm.lean»

lean_lib Main

@[default_target]
lean_exe «llm.lean» {
  root := `Main
}
