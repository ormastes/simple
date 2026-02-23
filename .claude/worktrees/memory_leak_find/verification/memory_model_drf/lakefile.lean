import Lake
open Lake DSL

package «memory_model_drf» where
  -- add package configuration options here

@[default_target]
lean_lib «MemoryModelDRF» where
  srcDir := "src"
  roots := #[`MemoryModelDRF]

lean_exe «memory_model_drf» where
  srcDir := "src"
  root := `Main
