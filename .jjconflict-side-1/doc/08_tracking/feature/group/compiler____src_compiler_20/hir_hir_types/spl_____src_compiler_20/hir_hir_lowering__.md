# compiler_—_`src/compiler/20.hir/hir_types.spl`_+_`src/compiler/20.hir/hir_lowering/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-004"></a>FR-COMPILER-004 | Module-scoped symbol tables for correct cross-module name isolation | The driver uses a single shared `HirLowering` instance with a flat global `SymbolTable` scope to lower all modules in sequence. When two modules export the same type name (e.g., `CompileOptions` in `driver_core_types.spl` and `backend_types | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
