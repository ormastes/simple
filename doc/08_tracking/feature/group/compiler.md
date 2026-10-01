# compiler

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-001"></a>FR-COMPILER-001 | Fix self-hosted binary missing CompileOptions field accessors | The self-hosted release binary (`bin/release/x86_64-unknown-linux-gnu/simple`) fails to resolve `CompileOptions.low_memory` and `CompileOptions.mode` at runtime, producing "Function 'CompileOptions.low_memory' not found"" and ""Function 'Comp" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
