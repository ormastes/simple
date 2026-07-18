# simpleos_pci/device_grants,_dma_syscalls,_and_net_backend_layer

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-NET-0009"></a>FR-NET-0009 | Gate SR-IOV and DMA on IOMMU-capable isolation | SR-IOV virtual functions and high-throughput DMA paths must only be exposed to user-space or exoskeleton drivers when the device grant includes an isolation domain. No-IOMMU systems may use trusted early-boot drivers, but must not advertise | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
