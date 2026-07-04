# `src/os/userlib/device.spl`,_network_drivers,_block_drivers,_and

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0008"></a>FR-NET-0008 | Share DMA buffer ownership with storage and display drivers | display/GPU drivers Promote the existing `SharedDmaBuffer` shape into a common driver contract so network, file/block, and display drivers can exchange caller-owned DMA buffers without copying through ordinary heap memory. The contract must | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
