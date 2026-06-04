# compiler_—_`src/compiler/20.hir/hir_lowering/`_+_`src/compiler/80.driver/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-003"></a>FR-COMPILER-003 | Add 2-pass import resolver to self-hosted HIR lowering | The self-hosted HIR lowerer (`HirLowering`) must mirror the Rust seed's two-pass import loading pipeline from `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`: | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
