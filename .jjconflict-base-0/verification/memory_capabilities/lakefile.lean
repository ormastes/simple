import Lake
open Lake DSL

package «memory_capabilities» where
  -- add package configuration options here

lean_lib «MemoryCapabilities» where
  -- add library configuration options here

@[default_target]
lean_exe «memory_capabilities» where
  root := `Main
