# compiler_—_import_resolver_/_name-resolution_pass

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-002"></a>FR-COMPILER-002 | Fix self-hosted import resolver: same-named structs in different modules shadow each other | When two structs share the same short name but live in different fully-qualified module paths (e.g., `compiler.common.driver_core_types.CompileOptions` vs `compiler.backend.backend.backend_types.CompileOptions`), the self-hosted compiler's  | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
