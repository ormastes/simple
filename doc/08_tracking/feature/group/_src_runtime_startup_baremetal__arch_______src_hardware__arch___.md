# `src/runtime/startup/baremetal/<arch>/`_+_`src/hardware/<arch>/`

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0005"></a>FR-DRIVER-0005 | Per-arch DMA cache-maintenance runtime (6 arches) | `src/lib/nogc_sync_mut/io/dma.spl` landed with arch-agnostic API and barrier-only interpreter fallbacks. Each supported arch needs a real runtime implementation of `rt_dma_alloc`, `rt_dma_free`, `rt_dma_virt_of`, `rt_dma_phys_of`, `rt_dma_s | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
