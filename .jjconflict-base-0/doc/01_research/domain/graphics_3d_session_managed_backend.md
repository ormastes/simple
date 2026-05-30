<!-- codex-research -->
# Graphics 3D Session Managed Backend Domain Research

Date: 2026-05-17
Status: domain research note

## Backend Findings

### Vulkan

Vulkan session state should be long lived: instance, physical/logical device, queues, command pools, descriptor/pipeline caches, allocator policy, and synchronization primitives. Vulkan synchronization is explicit; memory dependencies and semaphore/fence ordering are part of the API contract. Timeline semaphores and external memory/semaphore support are important for interop and multi-queue scheduling.

Sources:
- Vulkan synchronization and cache control: https://docs.vulkan.org/spec/latest/chapters/synchronization.html
- Vulkan 1.4 specification: https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html
- Vulkan external memory/synchronization guide: https://docs.vulkan.org/guide/latest/extensions/external.html
- Vulkan device groups guide: https://docs.vulkan.org/guide/latest/extensions/device_groups.html

### CUDA

CUDA can directly render into CUDA-owned buffers or arrays with kernels. On Windows, display without CPU readback requires graphics interop: CUDA external memory and external semaphores can interoperate with APIs including Direct3D 11/12 and Vulkan through native handles. CUDA should therefore be modeled as a compute/render backend with explicit interop present paths, not as a standalone window-system presentation backend.

Sources:
- CUDA interoperability with graphics APIs: https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/graphics-interop.html
- CUDA C++ Programming Guide: https://docs.nvidia.com/cuda/cuda-programming-guide/
- Direct3D 12 multi-engine synchronization: https://learn.microsoft.com/en-us/windows/win32/direct3d12/user-mode-heap-synchronization

### Metal

Metal session state should include `MTLDevice`, command queues, resource heaps, pipeline states, command encoders, and synchronization policy. Apple’s current Metal documentation distinguishes newer Metal 4 `MTL4*` command APIs from original `MTL*` APIs, so the Simple API should hide those differences behind backend capability records.

Sources:
- Metal resource synchronization: https://developer.apple.com/documentation/metal/resource_synchronization
- Understanding the Metal 4 core API: https://developer.apple.com/documentation/metal/understanding-the-metal-4-core-api

### WebGPU

WebGPU maps naturally to persistent session objects: adapter/device/queue, command encoders, buffers, textures, bind groups, and pipeline caches. Browser and native WebGPU paths should expose the same high-level Simple capability model, with browser-only limits recorded in the session capability result.

Sources:
- W3C WebGPU specification: https://www.w3.org/TR/webgpu/
- MDN `GPUQueue.submit()`: https://developer.mozilla.org/en-US/docs/Web/API/GPUQueue/submit

## Cross-Backend Design Implications

- The common API should represent device/session ownership, queue ownership, synchronization, memory heaps, surface/present capabilities, and readback policy explicitly.
- Managed mode should retain and share expensive objects only within the same session generation and policy.
- Perf mode should allocate isolated queues/allocators/caches and reject attempts to borrow managed resources.
- CPU-only mode remains a first-class backend and uses the same session/probe/perf contract without GPU handles.
- ARM/RISC-V 32/64 support needs architecture capability records for SIMD width, cache-line assumptions, atomic support, icache flush hooks, and optional vector/JIT support.
