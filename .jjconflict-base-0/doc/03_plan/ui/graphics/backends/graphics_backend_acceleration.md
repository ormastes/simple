<!-- codex-design -->
# Graphics Backend Acceleration Agent Plan

Date: 2026-05-16
Status: Candidate plan pending requirement selection

Agents are not alone in the codebase. Each agent owns a disjoint write scope and must not revert edits outside that scope.

## Agent A: Backend Probe Contract

Ownership:
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`

Tasks:
- Add `BackendProbeResult`.
- Add strict backend creation with no fallback.
- Keep current fallback API compatible.

## Agent B: Vulkan Backend Repair

Ownership:
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
- Vulkan shader asset/wrapper modules

Tasks:
- Stop depending on unsupported GLSL runtime compilation.
- Add SPIR-V or feature-gated shader compiler path.
- Add clear/rect/readback smoke.

## Agent C: CUDA Backend Proof

Ownership:
- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl`
- CUDA strict smoke tests

Tasks:
- Prove device memory rendering and readback.
- Add diagnostics for unavailable feature/device.
- Document Windows CUDA compute and future D3D interop present.

## Agent D: Metal Backend Proof

Ownership:
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl`
- macOS Metal smoke tests

Tasks:
- Prove command queue, pipeline, dispatch, completion, and readback.
- Keep Linux unavailable diagnostics typed.

## Agent D2: OpenCL Backend Proof

Ownership:
- `src/runtime/runtime_simd_dispatch.c`
- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_opencl.spl`
- `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl`
- `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl`
- OpenCL strict smoke tests

Tasks:
- Replace stub-like OpenCL ICD hooks with real context, queue, program, kernel,
  enqueue, finish, and typed error reporting.
- Prove unavailable/build-failed/submit-failed/sync-failed/readback-failed
  states separately.
- Add generated fill/checksum kernel proof before broader 2D acceleration.
- Keep CPU fallback out of strict OpenCL success paths.

Implementation order:
1. Implement `rt_opencl_*` calls in `src/runtime/runtime_simd_dispatch.c` or a
   CUDA-runtime-equivalent Rust bridge.
2. Wire `src/lib/nogc_sync_mut/gpu/engine2d/sffi_opencl.spl` to those calls.
3. Make `opencl_session.spl` produce typed init/load/launch/sync/readback
   evidence.
4. Update `backend_probe.spl` and `engine.spl` only after runtime/session
   evidence proves OpenCL is not a CPU fallback.
5. Add generated artifact support and compiler target validation after runtime
   loading is real.

## Agent E: WebGPU/wgpu Runtime Proof

Ownership:
- `src/runtime/hosted/webgpu.rs`
- `src/runtime/hosted/Cargo.toml`

Tasks:
- Make stub mode explicit.
- Add `webgpu-real` proof and adapter diagnostics.

## Agent F: CPU SIMD and Optimization Plugin Linkage

Ownership:
- `src/compiler/60.mir_opt/`
- `src/compiler/70.backend/backend/native/x86_64_simd.spl`

Tasks:
- Add rendering optimization provider metadata.
- Gate by target features.
- Prevent broad unused SIMD extern linkage.

## Agent G: Duplication Reduction

Ownership:
- shared Engine2D helper modules

Tasks:
- Extract clip/mask, pixel packing, text fallback, upload/download, and availability helpers after tests exist.

## Agent H: System Test and CI Matrix

Ownership:
- `doc/03_plan/sys_test/graphics_backend_acceleration.md`
- backend-specific smoke tests

Tasks:
- Separate unavailable, fallback, and hardware execution statuses.
- Add perf fields for init, command, readback, artifact format, runtime state,
  fallback reason, and RSS.

## Agent I: Direct 2D C vs Simple Performance

Ownership:
- `test/05_perf/graphics_2d/`

Tasks:
- Build matched C and Simple scene runners.
- Record frame timing, pixels/sec, draw calls/sec, RSS, binary size, and pixel hash.
- Report `simple_vs_c_ratio`.

## Agent J: Simple GUI App vs Rust+Tauri Performance

Ownership:
- `test/05_perf/tauri_equiv/`

Tasks:
- Implement equivalent workflows: startup, new window, close, resize, scroll, route change, IPC, event broadcast, idle.
- Report Tauri renderer identity and Simple backend identity.
- Report p50/p95 plus RSS and idle CPU.

## Agent K: Chrome vs Simple Web Render Performance

Ownership:
- `test/05_perf/web_render_chrome/`

Tasks:
- Add Chrome fixture runner and Simple fixture runner.
- Capture Chrome FPS/dropped-frame/GPU raster/memory when available.
- Capture Simple parse/style/layout/paint/composite/present timings.
- Report `simple_vs_chrome_ratio` and pixel status.

## Agent L: Window Manager Optimization

Ownership:
- `src/os/compositor/`
- host WM bridge modules

Tasks:
- Replace tight present loop with event pump/sleep where possible.
- Add dirty-rect tracking and present batching.
- Add timing counters for event wait, input, layout, paint, present, idle.

## Agent M: Rendering Optimization Plugin Providers

Ownership:
- `src/compiler/60.mir_opt/`
- `src/compiler/85.mdsoc/feature/optimization/`

Tasks:
- Add provider metadata for rendering SIMD/vectorization.
- Add provider hit/change counters to perf reports.
- Ensure C-vs-Simple and Tauri-equivalent reports list active providers.

## Agent N: Normalized Backend Comparison Harness

Ownership:
- `test/05_perf/backend_compare/`
- parsers for existing startup, web-size, Tauri, Electron/Node, and graphics_2d
  reports

Tasks:
- Define `BackendComparisonSample` report rows.
- Normalize existing probe outputs without deleting backend-native reports.
- Reject ratio comparisons when fixture, viewport, sample count, warmup count,
  compiler mode, hardware identity, or backend selection policy differ.
