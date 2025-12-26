import Lake
open Lake DSL

package nogc_compile where
  srcDir := "src"

@[default_target]
lean_lib NogcCompile
