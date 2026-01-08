import Lake
open Lake DSL

package type_inference_compile where
  srcDir := "src"

@[default_target]
lean_lib TypeInferenceCompile

lean_lib Generics

lean_lib GenericsTest

lean_lib Contracts

lean_lib ContractsTest

lean_lib AsyncEffectInference

lean_lib Classes

lean_lib Traits

lean_lib ClassTraitIntegration

lean_lib Mixins

lean_lib MixinsTest

lean_lib MixinVerificationGenerated
