import Lake
open Lake DSL

package async_compile where
  srcDir := "src"

@[default_target]
lean_lib AsyncCompile
