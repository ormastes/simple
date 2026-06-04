# plugin_/_15.blocks

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-PLUG-0002"></a>FR-PLUG-0002 | `.so` block-proxy constructor for `activate_plugin` | constructs+registers it for each `"block:""` manifest entry via `spl_dlsym` in `src/compiler/15.blocks/plugin_startup.spl` (see `activate_plugin` loop, FR-PLUG-0002 DONE comment). `TODO-FR-PLUG-0003-COMPATIBLE` at line 267 intentionally left" | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
