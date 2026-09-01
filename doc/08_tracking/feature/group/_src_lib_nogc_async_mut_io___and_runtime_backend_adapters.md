# `src/lib/nogc_async_mut/io/`_and_runtime_backend_adapters

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0004"></a>FR-NET-0004 | Add packet I/O backend boundary for AF_XDP or DPDK | Define a packet I/O backend boundary that can drive RX/TX rings through AF_XDP or DPDK while preserving the portable socket backend. This should be capability-gated and excluded from default QEMU CI unless explicitly enabled. | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
