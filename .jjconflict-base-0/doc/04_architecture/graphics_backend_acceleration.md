<!-- codex-design -->
# Graphics Backend Acceleration Architecture

Date: 2026-05-16
Status: Candidate architecture pending requirement selection

## Goal

Make Simple graphics acceleration measurable and comparable:

- direct 2D Simple vs C;
- Simple GUI web-engine app vs Rust+Tauri;
- Simple web renderer vs Chrome;
- CPU SIMD via optimization providers;
- forced Vulkan, CUDA, Metal, WebGPU, and CPU-only backend proof.

## Proposed Layers

```text
performance fixture
  -> reference runner: C | Rust+Tauri | Chrome
  -> Simple runner: Engine2D | Simple GUI app | Simple web renderer
  -> trace normalizer
  -> report: correctness, timing, memory, backend, optimizer facts

Simple GUI / web / direct 2D
  -> window manager + RenderSurfaceBridge
  -> web renderer / Engine2D facade
  -> RenderBackendCore + RenderBackendAdv
  -> cpu-scalar | cpu-simd | cuda | vulkan | metal | webgpu
  -> runtime FFI / native driver API
```

## Backend Diagnostics

Add a shared probe result:

```text
BackendProbeResult:
  requested_name
  selected_name
  status
  device_name
  api_name
  feature_gate
  shader_format
  fallback_reason
```

Strict creation must fail rather than fallback when a requested backend cannot run a minimal command.

## Backend Rules

- CUDA: CUDA Driver API compute path; future Windows no-readback present should use CUDA/D3D interop.
- Vulkan: use SPIR-V or add a real shader compiler; stop relying on unsupported GLSL runtime compile.
- Metal: macOS-only native compute path with command queue, compute pipeline, buffer/texture, encoder dispatch, completion, readback/present.
- WebGPU/wgpu: portable backend with explicit `webgpu-real` proof; not a substitute for direct Vulkan/Metal/CUDA proof.
- CPU SIMD: CPU backend capability, not a duplicated backend family.

## Window Manager Rules

- Replace tight present loops with event pump/sleep where possible.
- Track dirty rectangles.
- Batch presents once per frame budget.
- Record event wait, input dispatch, layout, paint, composite, present, idle, and RSS.
- Benchmark new-window creation separately from child first paint.

## Simple GUI vs Rust+Tauri Rules

- Use equivalent user-visible workflows.
- Report Tauri renderer identity: WebView2/Chromium, WKWebView/WebKit, or WebKitGTK.
- Report Simple backend identity: CPU scalar, CPU SIMD, Vulkan, CUDA, Metal, or WebGPU.
- Compare startup, new window, close, resize, scroll, route change, IPC, event broadcast, idle CPU, and memory.

## Chrome Comparison Rules

- Use fixed fixtures, viewport, fonts, and assets.
- Capture Chrome FPS/dropped-frame/GPU raster/memory data where available.
- Capture Simple phase timings with matching categories.
- Store pixel diff and timing report together.

## Optimization Plugin Rules

Rendering optimizations must be declared as Simple optimization providers:

- span fill/copy vectorization;
- alpha blend vectorization;
- bounds-check elimination for clipped spans;
- paint-command exact dispatch cache;
- layout/style loop hoisting;
- target-feature metadata for SSE2, AVX2, NEON, or platform equivalent.

