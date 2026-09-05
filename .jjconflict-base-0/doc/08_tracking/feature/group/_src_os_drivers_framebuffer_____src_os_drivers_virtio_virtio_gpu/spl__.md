# `src/os/drivers/framebuffer/`,_`src/os/drivers/virtio/virtio_gpu.spl`,

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-DRIVER-0011"></a>FR-DRIVER-0011 | VGA/BGA framebuffer and VirtIO-GPU DMA acceleration boundary | compositor/display services Separate legacy VGA/BGA framebuffer acceleration from VirtIO-GPU DMA acceleration. VGA/BGA should use write-combining framebuffer mapping, dirty rectangles, and bounded blits. VirtIO-GPU should use the shared DMA | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
