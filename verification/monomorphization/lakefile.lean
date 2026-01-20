import Lake
open Lake DSL

package «monomorphization» where
  -- Monomorphization correctness verification

@[default_target]
lean_lib «MonomorphizationCorrectness» where
  srcDir := "src"
  roots := #[`MonomorphizationCorrectness]
