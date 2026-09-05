# compiler_loader_surfaces_in_`src/compiler/99.loader/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-COMPILER-011"></a>FR-COMPILER-011 | Share loader core logic only across proven safe seams | The compatibility loader in `src/compiler/99.loader/module_loader.spl` and the lifecycle-aware runtime loader in `src/compiler/99.loader/loader/module_loader.spl` should share core unload and reload bookkeeping only where the behavior is pr | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
