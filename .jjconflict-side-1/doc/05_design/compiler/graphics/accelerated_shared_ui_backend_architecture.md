<!-- codex-design -->
# Accelerated Shared UI Backend Architecture - Detail Design

Date: 2026-06-04
Status: Active detail design for staged implementation

## Core Data Structures

### Shared UI

- `SemanticUiTree`: stable widget IDs, kind, role, focus state, enabled state,
  text, geometry hints, and backend-neutral properties.
- `SemanticUiCommand`: click, type, submit, focus, resize, key, action, drag,
  scroll, and host-window command envelope.
- `SurfaceAdapter`: maps semantic tree/commands to native TUI, pure Simple GUI,
  pure Simple web, Tauri, Electron, and NodeJS/browser transports.

### Render And Compute

- `RenderArtifact`: shared HTML/snapshot/patch/pixel/capture artifact with
  target, surface ID, dimensions, scale, color space, and provenance.
- `Engine2DCommandStream`: normalized 2D primitive stream for fill, blit, line,
  text, image, clip, mask, scroll, and compositing operations.
- `GpuOffloadArtifact`: compiler output with backend, source format, binary
  format, target environment, entrypoint, ABI layout, feature requirements, and
  build diagnostics.
- `BackendComparisonSample`: normalized evidence row with backend family,
  shell/backend name, cold/warm start, binary/package bytes, p50/p95 frame time,
  p95 input-to-paint, RSS, artifact build/load/submit/sync/readback timing,
  checksum, fallback state, and unavailable reason.

## Algorithms

### UI Adapter Normalization

1. Build `SemanticUiTree` from application state.
2. Emit a semantic command log before transport-specific serialization.
3. Let each adapter convert the command to its transport format:
   terminal event, HTTP/WebSocket request, Electron IPC, Tauri event, or
   NodeJS/browser message.
4. After each command, capture semantic state and optional render artifacts.
5. Equality compares semantic state first, then capture/pixel evidence.

### Tagged GPU Offload

1. Parse `@gpu`/`kernel fn` target metadata into a backend target set.
2. Run shared GPU subset checks.
3. Run target-specific checks:
   CUDA/NVPTX intrinsics, OpenCL address spaces and barrier legality, SPIR-V
   environment rules, and CPU SIMD fallback legality.
4. Emit backend artifacts:
   PTX for CUDA, OpenCL C or OpenCL SPIR-V for OpenCL, SPIR-V for Vulkan,
   metallib/MSL for Metal where supported.
5. Register artifact metadata with `generated_kernel_dispatch.spl`.
6. Runtime probes load, submit, synchronize, and read back with typed evidence.

### Normalized Benchmark Collection

1. Run existing focused probes unchanged.
2. Parse their native output into `BackendComparisonSample`.
3. Attach hardware, OS, compiler mode, feature flags, and optimization-provider
   metadata.
4. Mark missing hardware as `unavailable`, missing artifact as
   `artifact-unavailable`, and checksum mismatch as `readback-mismatch`.
5. Aggregate p50/p95 and max RSS only after sample count and fixture identity
   match.

## Error Handling

- Backend unavailable: no device/runtime/ICD/webview found.
- Artifact unavailable: compiler did not emit the target artifact.
- Artifact invalid: wrong magic, missing entrypoint, unsupported target
  environment, or build failure.
- Submit failed: runtime loaded the artifact but could not enqueue work.
- Readback failed: work submitted but no valid checksum/pixels were produced.
- Fallback used: lower-priority backend executed; report must preserve the
  preferred backend and fallback reason.

## Implementation Sequence

1. Freeze the shared semantic UI contract and prove adapter equivalence before
   adding more host-specific render behavior.
2. Route pure Simple GUI/web render requests through the shared web render API
   and require any pixel/capture path to report whether it reached Engine2D.
3. Add Engine2D backend conformance tests for CPU, Metal, CUDA, OpenCL, Vulkan,
   and software unavailable states. Hardware absence is a typed result, not a
   hidden pass.
4. Complete OpenCL runtime evidence against existing `opencl_session.spl` and
   keep ICD unavailable, artifact unavailable, build failure, enqueue failure,
   and readback mismatch as separate states.
5. Extend compiler artifact metadata and GPU checker target validation now that
   the Rust CLI can emit CUDA PTX, OpenCL C, and HIP C++ artifacts.
6. Add normalized performance harness and report schema for startup, package
   size, frame latency, RSS, artifact build/load/submit/sync/readback, and
   fallback reason.
7. Backend-by-backend implementation: CPU SIMD, CUDA, OpenCL, Vulkan, Metal,
   WebGPU, pure Simple shell, Tauri, Electron, NodeJS/browser.
8. System tests, generated manuals, and release verification.

## Current Implementation Evidence

| Area | Evidence | Status |
|---|---|---|
| CUDA compiler output | `bin/simple compile --backend=cuda|ptx` routes to PTX | Present |
| OpenCL compiler output | `test/03_system/compiler/opencl_backend_cli_smoke_spec.spl` | Present |
| HIP compiler output | `test/03_system/compiler/hip_backend_cli_smoke_spec.spl` | Present |
| Kernel metadata | Rust parser preserves `kernel` as an attribute | Present |
| OpenCL/HIP runtime trait | `src/compiler_rust/gpu/src/backend/{rocm,cuda}.rs` | Partial runtime support |
| Pure Simple HIP backend | `src/compiler/70.backend/backend/hip_backend.spl` reports generic MIR lowering unavailable | Honest contract |
| Shared UI requirements | `doc/02_requirements/ui/misc/shared_wm_renderer_unification.md` | Selected full convergence path |

## Verification Gates

- `bin/simple check` for new specs before running them.
- CLI smoke specs for each emitted GPU artifact format.
- Engine2D conformance spec must assert both capability metadata and rendering
  or typed unavailable state.
- Semantic UI parity spec must compare state and command result before pixels.
- Performance samples must include fixture ID, backend ID, device/host facts,
  sample count, cold/warm startup, binary size, p50/p95 latency, max RSS, and
  fallback reason.
