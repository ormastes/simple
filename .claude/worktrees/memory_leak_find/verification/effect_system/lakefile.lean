import Lake
open Lake DSL

package «effect_system» where
  -- Effect system safety verification

@[default_target]
lean_lib «EffectSafety» where
  srcDir := "src"
  roots := #[`EffectSafety]
