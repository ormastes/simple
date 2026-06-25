# plugin_/_70.backend.cranelift

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-PLUG-0004"></a>FR-PLUG-0004 | Static lowering / fusion of sugar rules through Cranelift | AC-3 v1 ships a *dynamic-load* sugar registry consulted by the interpreter. The `[STATIC-NEXT]` marker at `c_backend_translate_ops.spl:145` (the Cranelift matmul emit site) is the insertion point for compile-time specialization: when a rule | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
