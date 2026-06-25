# nvme,_virtio-blk,_vfs/fs-driver_interface

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0010"></a>FR-DRIVER-0010 | DMA-backed file/block driver direct I/O path | Add a direct I/O path for file and block drivers where callers can pass a shared DMA buffer to read/write without copying through intermediate VFS heap buffers. Buffered file APIs remain the default; direct I/O must require an explicit flag | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
