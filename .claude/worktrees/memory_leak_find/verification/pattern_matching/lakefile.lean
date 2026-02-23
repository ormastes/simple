import Lake
open Lake DSL

package «pattern_matching» where
  -- Pattern matching exhaustiveness verification

@[default_target]
lean_lib «PatternExhaustiveness» where
  srcDir := "src"
  roots := #[`PatternExhaustiveness]
