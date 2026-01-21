import Lake
open Lake DSL

package «mixin_verification» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «MixinVerification» where
  srcDir := "src"
