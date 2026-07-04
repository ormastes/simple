<!-- codex-research -->
# Simple 3D Graph IR Domain Research

## Primary Sources

- Vulkan command buffers record bind, draw, dispatch, copy, and synchronization
  commands before queue submission:
  https://docs.vulkan.org/spec/latest/chapters/cmdbuffers.html
- Vulkan descriptor sets bind resources for later pipeline commands and remain
  part of command-buffer state:
  https://docs.vulkan.org/spec/latest/chapters/descriptorsets.html
- Vulkan dynamic rendering lets color/depth attachment formats be supplied
  directly when creating pipelines and recording commands:
  https://docs.vulkan.org/tutorial/latest/03_Drawing_a_triangle/02_Graphics_pipeline_basics/03_Render_passes.html
- CUDA exposes kernels, device memory spaces, and streams; streams provide
  ordered dependency lanes for kernel launches and copies:
  https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html
- WebGPU uses command encoders, render pass encoders, render pipelines, vertex
  and index buffers, and bind groups:
  https://www.w3.org/TR/webgpu/

## Synthesis

Modern 3D APIs converge on explicit state recording: passes/attachments,
pipelines, resource bindings, and draw or dispatch actions. A Simple 3D Graph IR
should preserve that shape without taking a dependency on one API. Vulkan and
WebGPU map naturally to render passes plus state-setting commands. CUDA maps
better to future compute graph nodes, streams, and buffer dependencies, not to
indexed graphics draws directly.

## Design Pressure

- Keep the first graph IR backend-neutral and handle-based.
- Sort draws within pass boundaries only; cross-pass reordering can violate
  attachment and synchronization semantics.
- Represent resources explicitly so future Vulkan descriptor/bind-group and CUDA
  stream/resource scheduling can reuse the same dependency surface.
- Fail closed on invalid handles by refusing to record invalid draws.
