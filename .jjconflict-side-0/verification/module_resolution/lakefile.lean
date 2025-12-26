import Lake
open Lake DSL

package module_resolution where
  srcDir := "src"

@[default_target]
lean_lib ModuleResolution
