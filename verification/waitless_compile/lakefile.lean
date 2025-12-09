import Lake
open Lake DSL

package waitless_compile where
  srcDir := "src"

@[default_target]
lean_lib WaitlessCompile
