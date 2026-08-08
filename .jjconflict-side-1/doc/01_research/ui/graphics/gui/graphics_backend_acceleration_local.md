<!-- codex-research -->
# Graphics Backend Acceleration Domain Research

Date: 2026-05-16

## Vulkan

Vulkan compute rendering should use SPIR-V shader modules or a real shader compilation step before pipeline creation. The current repo mismatch is that Simple-side Vulkan uses GLSL strings while the runtime rejects GLSL compilation.

Sources:
- https://docs.vulkan.org/spec/latest/chapters/shaders.html
- https://docs.vulkan.org/spec/latest/appendices/spirvenv.html

## CUDA

The plan is CUDA Driver API based, not NVAPI based. The direct render path is:

```text
Engine2D draw call
-> CUDA kernel
-> device framebuffer
-> sync/readback or future graphics interop present
```

For Windows, CUDA compute can use `nvcuda.dll`. Efficient presentation should later use CUDA/D3D11 or CUDA/D3D12 interop rather than CPU readback.

Source:
- https://docs.nvidia.com/cuda/cuda-driver-api/group__CUDA__MODULE.html

## Metal

Metal is in scope for macOS. The backend should use `MTLDevice`, `MTLCommandQueue`, `MTLComputePipelineState`, buffers/textures, a compute command encoder, dispatch, command buffer completion, and readback or native surface presentation.

Sources:
- https://developer.apple.com/documentation/metal/mtlcomputecommandencoder
- https://developer.apple.com/library/archive/documentation/Miscellaneous/Conceptual/MetalProgrammingGuide/Compute-Ctx/Compute-Ctx.html

## WebGPU / wgpu

`wgpu` can provide a portable native WebGPU-style path over Vulkan, Metal, D3D12, OpenGL, WebGL2, or WebGPU depending on platform support. It is useful as a portable backend but should not be treated as proof that direct Vulkan, Metal, or CUDA backends are working.

Source:
- https://wgpu.rs/doc/wgpu/index.html

## Rust + Tauri Baseline

Tauri uses Rust plus TAO/WRY and system webviews. On Windows, Tauri uses WebView2 based on Microsoft Edge/Chromium. macOS/iOS and Linux use WebKit-family webviews.

Sources:
- https://tauri.app/reference/javascript/api/namespacewebview/
- https://v2.tauri.app/reference/webview-versions/

Implication: Simple GUI app vs Tauri app comparison is a desktop-workflow benchmark, not a same-renderer benchmark. Reports must identify the renderer/backend on both sides.

## Chrome Baseline

Chrome DevTools exposes FPS, dropped or partially-presented frames, GPU raster state, GPU memory, and scroll-performance diagnostics. web.dev recommends INP-style responsiveness: time from user interaction until the next visual response can be painted.

Sources:
- https://developer.chrome.com/docs/devtools/rendering/performance
- https://developer.chrome.com/docs/devtools/performance/reference/
- https://web.dev/articles/inp
- https://web.dev/rendering-performance/

Implication: Simple web-rendering benchmarks should normalize phases to input, script/event, style/layout, paint/raster, composite/present.

## Recommended Comparison Pattern

| Simple Surface | Reference | Claim Allowed |
|---|---|---|
| Direct 2D | C | Engine/compiler/runtime overhead and pixel throughput |
| GUI app | Rust + Tauri | Desktop workflow parity: startup, windows, scroll, IPC, memory |
| Web renderer | Chrome | Browser rendering timing and compatibility |
| CPU SIMD | CPU scalar + C | Optimization-provider effectiveness |
| GPU backend | CPU reference | Backend correctness and acceleration |

