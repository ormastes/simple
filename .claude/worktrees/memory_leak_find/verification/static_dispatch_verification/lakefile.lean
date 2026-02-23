import Lake
open Lake DSL

package «static_dispatch_verification» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «StaticDispatchVerification» where
  srcDir := "src"
