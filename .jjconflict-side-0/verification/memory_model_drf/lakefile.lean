import Lake
open Lake DSL

package «memory_model_drf» where
  -- add package configuration options here

lean_lib «MemoryModelDRF» where
  -- add library configuration options here

@[default_target]
lean_exe «memory_model_drf» where
  root := `Main
