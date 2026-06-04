# plugin_/_compiler_/_di

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-PLUG-0005"></a>FR-PLUG-0005 | DI runtime-slot plugin loader integration | found in any `.spl` source. `src/compiler/00.common/di_runtime.spl` is a string-keyed lazy engine (`di_register`/`di_resolve`) — no slot syntax. `src/compiler/00.common/di_config.spl` parses `config/di.sdn` for `DiServiceConfig` entries but | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
