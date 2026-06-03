<!-- codex-design -->
# Accelerated Shared UI Backend Architecture - Detail Design

Date: 2026-06-03
Status: Candidate design pending requirement selection

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

1. Requirements selection for feature/NFR options.
2. Shared UI semantic contract update.
3. OpenCL runtime completion against existing `opencl_session.spl`.
4. OpenCL compiler artifact design and GPU checker target validation.
5. Normalized performance harness and report schema.
6. Backend-by-backend implementation: CPU SIMD, CUDA, OpenCL, Vulkan, Metal,
   WebGPU, pure Simple shell, Tauri, Electron, NodeJS/browser.
7. System tests and generated manuals.
