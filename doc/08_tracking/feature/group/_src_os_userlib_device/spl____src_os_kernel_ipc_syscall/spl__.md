# `src/os/userlib/device.spl`,_`src/os/kernel/ipc/syscall.spl`,

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0009"></a>FR-DRIVER-0009 | Shared DMA descriptor contract for net, file, and display drivers | driver framework capability surfaces Define one shared DMA descriptor contract for all high-throughput drivers: network RX/TX rings, storage direct I/O, and display/GPU transfer buffers. The descriptor must carry CPU virtual address, device | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
