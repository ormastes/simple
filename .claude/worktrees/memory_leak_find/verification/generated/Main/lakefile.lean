import Lake
open Lake DSL

package «generated_main» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

@[default_target]
lean_lib «GeneratedMain» where
  srcDir := "."
  roots := #[`Main.MemorySafety]
