<!-- codex-design -->
# Graphics Backend Acceleration Detail Design

Date: 2026-05-16
Status: Candidate detail design pending requirement selection

## Workstream 1: Backend Probe Contract

Add `BackendProbeResult` and strict backend creation APIs under Engine2D. Existing fallback APIs remain compatible.

## Workstream 2: Vulkan Repair

Replace the unsupported GLSL runtime compile path with precompiled SPIR-V assets or a feature-gated shader compiler. Near-term preference: SPIR-V assets for fixed 2D kernels.

## Workstream 3: CUDA Proof

Add strict CUDA smoke proving device count, context, memory allocation, PTX load, kernel lookup, launch, sync, readback, and CPU pixel parity.

## Workstream 4: Metal Proof

Add macOS-only strict Metal smoke proving device, command queue, compute pipeline, dispatch, completion, and readback.

## Workstream 5: WebGPU/wgpu Proof

Keep default stub mode explicit. Add `webgpu-real` proof for adapter/device/off-screen texture upload, present/readback, and backend diagnostics.

## Workstream 6: CPU SIMD Integration

Treat SIMD as CPU backend capability:

- scalar CPU is reference;
- SIMD kernels accelerate contiguous fill, copy, alpha blend, and scroll;
- optimization provider metadata declares target filters and required facts.

## Workstream 7: Duplication Reduction

After tests exist, extract shared clip/mask helpers, pixel packing, glyph/text fallback, host/device upload/download helpers, and availability diagnostics.

## Workstream 8: Direct C vs Simple 2D Benchmark

Create `test/perf/graphics_2d/`:

- `c_ref/` dependency-light C renderer;
- `simple/` Simple Engine2D renderer;
- `fixtures/` shared scene descriptions;
- `report/` ratio and pixel-hash output.

Scenes:

- clear-only;
- rect-fill throughput;
- line/circle mixed primitives;
- text list;
- image blit;
- scaled image blit;
- clipped scroll list;
- dirty-rect dashboard update.

Optimization path:

- hoist repeated bounds/clip checks;
- specialize contiguous span fill/copy;
- add SIMD fill/copy/blend/scroll kernels;
- pass CPU/features to native/LLVM output;
- measure scalar, SIMD, and GPU separately.

## Workstream 9: Simple GUI App vs Rust+Tauri Benchmark

Create `test/perf/tauri_equiv/`:

- Rust+Tauri reference app;
- Simple GUI app using Simple web engine and WM bridge;
- common workflow driver.

Workflows:

- cold start to first paint;
- open new window;
- close new window;
- resize;
- scroll 10k rows;
- route/page switch;
- IPC command round trip;
- event broadcast to two windows;
- idle CPU/RSS after 60 seconds.

Optimization path:

- event-loop sleep instead of tight present loop;
- frame-batched input and paint;
- layout/style cache;
- dirty-rect scroll and dashboard updates;
- patch batches instead of full snapshot resend;
- cached command/event lookup tables.

## Workstream 10: Simple Web Renderer vs Chrome Benchmark

Create `test/perf/web_render_chrome/` and extend compatibility fixtures with timing:

- static app shell;
- large-list scroll;
- sticky header/sidebar;
- selector stress;
- canvas/WebGPU surface;
- JS route switch.

Optimization path:

- subtree style/layout invalidation;
- scroll damage tracking;
- paint command batching;
- glyph cache;
- GPU upload batching;
- lower allocations in selector matching and layout walks.

## Workstream 11: Simple Optimization Plugin Integration

Add provider metadata and counters for rendering hot paths:

- vectorized span fill/copy;
- vectorized alpha blend;
- proven clipped-span bounds elimination;
- exact dispatch cache for paint commands;
- loop-invariant hoisting in layout/style;
- target-feature gates.

## Acceptance Gates

- Strict backend tests fail on fallback.
- Vulkan no longer calls unsupported GLSL compile path.
- CUDA hardware smoke passes on NVIDIA when feature-enabled.
- Metal strict smoke exists and is macOS-gated.
- WebGPU real-mode smoke exists and stub behavior is explicit.
- C vs Simple 2D report exists with ratios and pixel hashes.
- Rust+Tauri vs Simple GUI report exists for startup, new-window, scroll, resize, IPC, and memory.
- Chrome vs Simple web render report exists with pixel and timing status.
- WM tight-loop behavior is replaced or explicitly benchmark-gated.

