import Lake
open Lake DSL

package «memory_capabilities» where
  -- add package configuration options here

@[default_target]
lean_lib «MemoryCapabilities» where
  srcDir := "src"
  roots := #[`MemoryCapabilities]

lean_exe «memory_capabilities» where
  srcDir := "src"
  root := `Main
