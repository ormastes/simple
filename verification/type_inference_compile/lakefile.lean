import Lake
open Lake DSL

package type_inference_compile where
  srcDir := "src"

@[default_target]
lean_lib TypeInferenceCompile

lean_lib Generics

lean_lib GenericsTest
