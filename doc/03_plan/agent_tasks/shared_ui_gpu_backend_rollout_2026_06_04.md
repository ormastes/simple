# Shared UI and GPU Backend Rollout Agent Plan

Date: 2026-06-04
Status: Active rollout plan

## Goal

Complete the requested convergence stack:

```text
semantic UI
  -> TUI / pure Simple GUI / pure Simple web / Tauri / Electron / Node-browser adapters
  -> shared web render API
  -> pure Simple web renderer
  -> Engine2D render API
  -> CPU scalar/SIMD, CUDA, OpenCL, HIP/ROCm, Vulkan, Metal, WebGPU backends
  -> tagged Simple GPU offload artifacts and measured evidence
```

## Current Evidence

| Area | Evidence |
|---|---|
| Shared UI requirements | `doc/02_requirements/ui/misc/shared_wm_renderer_unification.md` |
| Architecture | `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md` |
| Detail design | `doc/05_design/compiler/graphics/accelerated_shared_ui_backend_architecture.md` |
| CUDA compiler artifact | Rust CLI routes `cuda` and `ptx` to PTX output |
| OpenCL compiler artifact | `test/03_system/compiler/opencl_backend_cli_smoke_spec.spl` |
| HIP compiler artifact | `test/03_system/compiler/hip_backend_cli_smoke_spec.spl` |
| Kernel tag propagation | `src/compiler_rust/parser/src/parser_impl/functions.rs` |
| Shared GPU source emitter | `src/compiler_rust/compiler/src/pipeline/codegen.rs` |

## Agent Teams

### Team A: Semantic UI and Surface Adapters

Ownership:

- `src/lib/common/ui/`
- `src/app/ui*/`
- `test/01_unit/app/ui/`
- `test/03_system/gui/`

Deliverables:

1. Freeze `semantic_contract.spl` as the backend-neutral widget, command,
   focus, event, capability, snapshot, and read-after-write contract.
2. Add adapter helpers for TUI, Web, Electron, Tauri, pure Simple GUI, and
   headless paths.
3. Add one parity spec that feeds the same fixture through each adapter helper
   and compares semantic state before transport-specific rendering.

Exit gate:

- A focused Simple check and system/unit run proves at least Web, TUI, Electron,
  Tauri, and headless helpers produce equivalent semantic command results.

Current evidence:

- `semantic_ui_render_target_evidence_matrix()` validates one semantic command
  and snapshot through `simple_web`, `tui_web`, `electron`, `tauri`,
  `headless`, and `pure_simple` transport envelopes without target-specific
  payload drift.
- `NoneBackend` now exposes semantic snapshot JSON and target-aware snapshot
  envelopes through the canonical `headless` web-render target, proving the
  no-display adapter participates in the same shared transport contract.
- `SemanticUiCommandDispatchEvidence` validates that click, type, and focus
  commands dispatch through `UISession.dispatch_semantic_command`, advance the
  access snapshot revision, and are visible through read-after-write access
  events for `simple_web`, `tui_web`, `electron`, `tauri`, `headless`, and
  `pure_simple`.
- Covered by
  `test/01_unit/app/ui/semantic_contract_spec.spl` and
  `test/01_unit/app/ui/semantic_render_transport_spec.spl`.

### Team B: Shared Web Renderer to Engine2D

Ownership:

- `src/lib/common/ui/web_render_api.spl`
- `src/app/ui.web/`
- `src/app/ui.render/`
- pure Simple browser/web renderer paths
- Engine2D API files under `src/lib/*/gpu/engine2d/`

Deliverables:

1. Ensure all GUI/web adapters create render requests through the shared web
   render API.
2. Add an Engine2D capture/capability field to render artifacts.
3. Add a pure Simple web renderer fixture that reports whether pixel output
   came from Engine2D, software compatibility, or unavailable state.

Exit gate:

- A system spec proves semantic state -> shared web render API -> pure Simple
  web renderer -> Engine2D capture or typed unavailable result.

Current evidence:

- `WebRenderArtifact` carries `engine2d_status`, `engine2d_backend`, and
  `engine2d_reason` for not-requested, compatibility, rendered, and unavailable
  states.
- `web_render_adapter_request()` is the shared render-request constructor used
  by Web, Electron, Tauri, and pure Simple browser adapters for target,
  surface, viewport, style, script, and body assembly.
- `WebRenderRequestProvenanceEvidence` validates that semantic JSON and shared
  artifacts agree on target, surface, dimensions, HTML output, IPC/pixel
  output, and Engine2D provenance for `simple_web`, `tui_web`, `electron`,
  `tauri`, `headless`, and `pure_simple`.
- `web_render_node_bitmap_fixture_artifact()` materializes valid pure Simple
  Node bitmap fixture evidence as an `engine2d_rendered` artifact and keeps
  target, dimension, or pixel-count mismatches as explicit compatibility
  provenance from `src/lib/common/ui/web_render_bitmap_evidence.spl`.
- Covered by
  `test/01_unit/app/ui/web_render_node_fixture_evidence_spec.spl` and
  `test/01_unit/app/ui/web_render_backend_api_spec.spl`.

### Team C: GPU Runtime Backends

Ownership:

- `src/compiler_rust/gpu/src/backend/`
- `src/compiler_rust/runtime/src/value/gpu*`
- `src/compiler_rust/runtime/src/cuda_runtime.rs`
- `src/lib/*/gpu/engine2d/*opencl*`
- runtime SFFI/ICD bindings

Deliverables:

1. Keep CUDA and ROCm/HIP behind the shared Rust `Backend` trait.
2. Add OpenCL context, queue, program build, kernel, enqueue, finish, and
   readback evidence with typed errors.
3. Keep device unavailable, ICD unavailable, artifact unavailable, build
   failure, submit failure, and checksum mismatch as distinct states.

Exit gate:

- OpenCL unavailable passes as a typed unavailable state.
- OpenCL available hosts produce load/build/enqueue/readback evidence without
  requiring CUDA hardware.

Current evidence:

- CUDA Engine2D runtime backend is split into a small facade, PTX kernel source
  module, launch-argument helpers, and extension facade while preserving the
  `CudaBackend` RenderBackend contract below the 800-line source guard.
- Vulkan SPIR-V placeholder helpers now keep the original
  `backend_vulkan_spirv` import surface as a probe/blob facade while secondary
  raster blobs live in `backend_vulkan_spirv_raster_blobs.spl`, bringing the
  facade below the 800-line source guard.
- CPU emulation fallback now keeps `backend_emu` as the compatibility facade
  while advanced image/blur/shadow/transform/blend helpers live in
  `backend_emu_adv.spl` and shared math helpers live in `backend_emu_math.spl`.
  The Engine2D backend directory has no source file above the 800-line refactor
  guard.
- Shared text blit payloads now construct foreground glyph pixels directly,
  which fixes CUDA/HIP/OpenCL-style image-blit text payloads that previously
  carried dimensions without visible foreground pixels on the interpreter path.
- CUDA, HIP/ROCm, and OpenCL generated Engine2D session launch paths share the
  same `Generated2DSessionLaunchGate` preflight for runtime readiness, module
  readiness, argument-buffer presence, operation support, dimensions, and
  backend-specific launch metadata.
- `Generated2DSessionRuntimeProvenance` now normalizes session-level CUDA,
  HIP/ROCm, and OpenCL generated-kernel provenance into one typed shape for
  launch API, entry, artifact, runtime availability, module/program
  availability, args readiness, and typed unavailable statuses such as
  `cuda-runtime-unavailable`, `hip-module-unavailable`, and
  `opencl-runtime-or-queue-unavailable`.
- CUDA, ROCm, and OpenCL sessions expose
  `launch_generated_2d_runtime_provenance()`, letting hardware-unavailable
  tests prove backend-specific session states without pretending a device
  launch occurred.
- `Generated2DOperationProvenance` compares CPU scalar/SIMD baseline work with
  generated CUDA/OpenCL operation readiness for vector fill, font/text blit,
  image blit, alpha blend, and scroll families. Text/font rows explicitly mark
  the CPU glyph-preprocess step while still tying GPU execution to the shared
  generated copy kernel and typed OpenCL unavailable states.
- OpenCL sessions now expose `read_buffer_evidence()` so buffer readback
  reports typed `missing-ffi`, `missing-queue`, `missing-buffer`,
  `missing-host-buffer`, `invalid-size`, `readback-failed`, matched checksum,
  and checksum mismatch states instead of collapsing runtime readback into a
  raw boolean.
- Covered by `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/opencl_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`,
  and `test/02_integration/rendering/cuda_strict_spec.spl`.

### Team D: Compiler Offload and Artifact Metadata

Ownership:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`
- Rust CLI compile commands
- `src/compiler/35.semantics/gpu_checker.spl`
- `src/compiler/70.backend/backend/{cuda_backend,opencl_backend,hip_backend,gpu_backend_metadata}.spl`
- compiler GPU tests

Deliverables:

1. Normalize CUDA PTX, OpenCL C, HIP C++, Vulkan SPIR-V, and future Metal/MSL
   artifacts into one metadata shape.
2. Validate explicit `@gpu(target=...)`, `kernel`, and `auto` backend requests.
3. Add target-specific diagnostics for CUDA-only, OpenCL-only, HIP-only, and
   unsupported shared-kernel features.

Exit gate:

- CLI smoke specs pass for CUDA/PTX, OpenCL C, and HIP C++.
- Negative specs prove unsupported target features are rejected with backend
  and reason.

Current evidence:

- `portable_compute_backend_targets_from_order()` resolves tagged backend order
  strings such as `cuda,opencl`, `rocm,cl,cuda`, and `auto` into one shared
  CUDA/HIP/OpenCL/Metal portable target request.
- `portable_compute_2d_optimization_backend_plan()` builds generated Engine2D
  optimization artifacts and compile plans from that request, while keeping
  unsupported names such as `vulkan` visible as a closed-plan diagnostic.
- `portable_compute_operation_metadata()` records compiler-side offload intent
  for explicit `@gpu`, `kernel`, and `auto` requests as normalized rows with
  target order, operation family, generated entry symbol, source format,
  binary artifact format, artifact suffix, CPU-preprocess requirement, and
  closed diagnostics for unsupported Vulkan SPIR-V or unsupported operation
  families.
- `GpuGenerated2DBackendCompileContract` exposes one generated Engine2D
  compile-contract shape for CUDA/PTX, HIP/HSACO, OpenCL/SPIR-V, and
  Metal/metallib artifact
  evidence; the existing HIP and OpenCL backend wrappers now delegate
  readiness, status, and diagnostic logic to that shared contract.
- `portable_compute_backend_target_diagnostic()` reports accepted CUDA, HIP,
  OpenCL, and Metal target aliases through the same shape and keeps Vulkan
  SPIR-V explicit as a closed portable-emitter request that belongs to the
  separate Vulkan backend.
- Covered by
  `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl`,
  `test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl`,
  and the HIP/OpenCL backend contract specs.

### Team E: Performance, Startup, and Binary Size Evidence

Ownership:

- `test/05_perf/`
- `scripts/check/check-startup-size-performance-audit.shs`
- `scripts/check/check-web-baremetal-size-audit.shs`
- `scripts/check/check-qt-gui-size-baseline.shs`
- `doc/09_report/`

Deliverables:

1. Define `BackendComparisonSample` as the normalized report row.
2. Convert existing startup, package size, graphics, Tauri, Electron, Node, and
   GPU artifact probes into that schema.
3. Record unavailable hardware/tooling as data, not as hidden success.

Exit gate:

- One report includes cold/warm startup, binary/package bytes, p50/p95 frame or
  request latency, max RSS, artifact build/load/submit/sync/readback timing,
  backend/device metadata, checksum or pixel proof, and fallback reason.

Current evidence:

- `BackendComparisonSample` in
  `src/app/wm_compare/backend_measurement_report.spl` is the normalized report
  row for shared UI, shell, GPU, startup, size, RSS, artifact timing,
  checksum/pixel proof, fallback, and unavailable-hardware evidence.
- `current_host_backend_comparison_samples()` converts repeated
  `/usr/bin/time` startup/RSS output plus binary/package sizes into normalized
  CPU SIMD, Metal, Vulkan, CUDA, OpenCL, and HIP sample rows, preserving
  unavailable GPU tooling as explicit sample data.
- `BackendComparisonSample` rows now carry compiler offload metadata:
  offload tag kind, operation family, generated operation, entry symbol,
  source format, binary artifact format, and artifact suffix. Current-host
  capture populates CUDA/OpenCL/HIP/Metal rows from
  `portable_compute_operation_metadata()` and marks CPU SIMD rows as baseline
  evidence.
- Initialized GPU `BackendComparisonSample` rows now also require runtime
  provenance: compute target, execution path, launch API, entry symbol,
  artifact name, and `ready` runtime status. A host-safe initialized OpenCL
  fixture proves compiler metadata, generated runtime provenance, artifact
  timings, scalar baseline comparison, checksum, and pixel proof can be carried
  together without requiring GPU hardware on the test host.
- `initialized_gpu_comparison_sample_from_measurement()` now accepts measured
  CUDA/OpenCL/HIP initialized runtime evidence directly: warmup/sample counts,
  p50/p95 frame timings, cold/warm startup, package/binary bytes, artifact
  build/load/submit/sync/readback timings, device ID, checksum, pixel proof,
  dimensions, and runtime/module/args readiness. The host-safe fixture delegates
  through this measured path so future real GPU runners and current tests share
  the same strict row construction and validation.
- `initialized_gpu_measurement_export_sdn()` and the
  `backend_measurement_export.spl --initialized-gpu-backend <lane>` CLI path
  export one measured initialized GPU row as normalized SDN. This gives a real
  CUDA/OpenCL/HIP runner a stable reporting interface without weakening the
  existing current-host unavailable-lane matrix.
- `initialized_gpu_runner_comparison_sample()` and
  `backend_measurement_export.spl --probe-initialized-gpu true` now probe the
  requested CUDA/OpenCL/HIP/ROCm lane before accepting measured values. The
  runner emits an initialized row only when the strict backend probe succeeds
  and the generated Engine2D runtime/module/args gate is ready; otherwise it
  emits an explicit unavailable/failed row with compiler/runtime metadata.
- `opencl_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-opencl-device-buffer true` now run
  the first backend-specific device-buffer capture path. It initializes an
  OpenCL session, loads generated `simple_2d_fill_u32` source, allocates a
  device buffer, launches/synchronizes/readbacks the generated fill kernel, and
  derives checksum/nonzero-pixel proof from the readback buffer. Hosts without
  a usable OpenCL context still emit a valid unavailable row with generated
  OpenCL metadata instead of silently falling back to CPU.
- `cuda_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-cuda-device-buffer true` now mirror
  the OpenCL path for CUDA PTX. It initializes a shared CUDA session, loads the
  generated Engine2D PTX module, allocates a device buffer, launches the
  generated fill kernel, synchronizes, copies device memory back to host memory,
  and records checksum/nonzero-pixel proof when CUDA is usable. Hosts without a
  usable CUDA runtime or device still emit a valid unavailable row with CUDA
  compiler/runtime metadata instead of falling back to CPU.
- `rocm_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-rocm-device-buffer true` now expose
  the same normalized measurement interface for HIP/ROCm. The row carries HIP
  compiler/runtime metadata, including HSACO format and `rt_rocm_launch_kernel`,
  and now gets its unavailable reason from `RocmSession` evidence backed by
  static interpreter `rt_rocm_*` hooks instead of a wm_compare-local placeholder.
  `RocmSession`/`RocmFfi` expose generated module load, kernel-handle launch
  with args pointer, synchronization, and readback evidence methods; dynamic HIP
  mode still fails closed for module/text and readback calls until the runtime
  owns safe HIP pointer and image contracts.
- `scripts/check/check-startup-size-performance-audit.shs` now also emits
  `startup_size_performance_audit_cuda_device_samples_*.sdn` and
  `startup_size_performance_audit_rocm_device_samples_*.sdn` and
  `startup_size_performance_audit_opencl_device_samples_*.sdn` through the
  CUDA/HIP/OpenCL device-buffer measurement paths, keeping startup/size samples
  and optional hardware-lane samples separate but generated by the same audit
  run.
- `scripts/check/check-startup-size-performance-audit.shs` now resolves the
  repository root correctly from `scripts/check`, captures nanosecond startup
  samples plus `/usr/bin/time` max RSS for the Simple standalone TUI lane, and
  emits a companion normalized backend-comparison SDN artifact with generated
  operation metadata.
- OpenCL, HIP, and ROCm now use the same acceleration-lane validation as CUDA,
  Metal, and Vulkan: initialized rows require scalar baseline comparison,
  strict rows reject GPU-to-CPU fallback, and initialized GPU samples require
  artifact build/load/submit/sync/readback timing evidence.
- Covered by
  `test/03_system/gui/wm_compare/backend_measurement_report_spec.spl` and
  `test/03_system/gui/wm_compare/backend_measurement_capture_spec.spl`.

## Integration Order

1. Team A and Team B establish the UI/render contract path.
2. Team C proves OpenCL runtime states and typed evidence.
3. Team D extends offload validation and metadata once runtime states are real.
4. Team E normalizes evidence after Teams A-C expose stable report fields.
5. Run release-blocking verification only after all generated specs are under
   `doc/06_spec/**/*.md` and `find doc/06_spec -name '*_spec.spl' | wc -l`
   returns `0`.

## Current Next Slice

The next smallest implementation slice is Team E HIP/ROCm runtime-backed generated-session parity:

1. Finish runtime-backed HIP module/readback parity by feeding real HSACO images
   into the static `rt_rocm_module_load` hook or adding a safe HIPRTC/hipcc
   compilation step, then populate readback proof on AMD hosts.
2. Connect initialized hardware rows to the normalized startup/bin-size
   report so perf comparison includes compiler metadata, runtime provenance,
   scalar baseline, and binary/package size evidence.
3. Preserve strict failure for fallback-to-CPU, missing compiler metadata,
   missing runtime-ready proof, missing artifact timings, or missing readback
   proof.
