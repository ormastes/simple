# `src/lib/nogc_async_mut/http_server/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0003"></a>FR-NET-0003 | Route HTTP static files through capability-driven sendfile | Use `IoDriver.net_capabilities()` to select the fastest safe static-file response path: `sendfile` or zero-copy where supported, async read plus send otherwise. The portable behavior must remain the default for QEMU and CI. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
