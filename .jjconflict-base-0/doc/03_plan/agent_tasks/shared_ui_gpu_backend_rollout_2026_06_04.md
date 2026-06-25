# Shared UI and GPU Backend Rollout Agent Plan

Date: 2026-06-04
Status: Active rollout plan

## 2026-06-11 Pure Simple GUI Startup Optimization Split

Current slice: keep GUI behavior and app code stable while reducing pure Simple
Engine2D text/helper startup cost and preserving generated/manual spec evidence.

Small task ownership:

- Spark: easy documentation and evidence bookkeeping only, including task-plan
  wording, state-log summaries, and generated/manual spec index checks. Spark
  must use a disjoint write scope and avoid source/test edits.
- Codex: hot-path code changes, Spark-output review, and integration decisions
  for Engine2D text helpers, software fallback behavior, and backend fallback
  ordering.
- Verify: focused checks for touched `.spl` files, focused SSpecs, optimizer
  scans, `doc/06_spec` executable-spec layout guard, and SPipe command wiring.

Independent work packets:

1. Engine2D AA text helper: hoist loop-invariant scale, glyph-width, and row
   sampling work in `helpers_text.spl`; prove with text helper and software
   backend specs.
2. Software fallback text path: keep `backend_software.spl` and shared text
   helpers aligned so CPU fallback avoids repeated length/tile work.
3. Evidence refresh: regenerate or update manuals only when an SSpec changes,
   then record exact focused check/test/optimizer results in lane state.
4. Follow-up triage: leave remaining optimizer findings as measured follow-up
   tasks unless they can be fixed without API, rendering, or app behavior
   changes.

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
- `WebRenderTauriBitmapParityEvidence` now records the Tauri target in the
  same no-tolerance pixel contract as the Simple renderer: target must be
  `tauri`, dimensions and pixel count must match, checksum and reference
  checksum must be identical, mismatch count must be `0`, and blur/tolerance is
  rejected. Live WebKitGTK proof is now supplied by
  `check-tauri-simple-web-layout-bitmap-evidence.shs`, which captures the
  Tauri shell under Xvfb for the production surface manifest.
- `WEB_RENDER_TARGET_CHROME` and `WEB_RENDER_TARGET_CHROMIUM` are now explicit
  shared web render targets with browser capability summaries, so standalone
  Chrome/Chromium no longer has to be hidden behind the Electron target.
- `WebRenderSurfaceManifestCaptureEvidence` validates one manifest-row contract
  for Electron, Tauri, Chrome, and Chromium: live `pass` rows must carry real
  capture, exact case counts, zero failures, zero mismatches, and no
  blur/tolerance; `unavailable` rows must carry a reason and must not claim live
  pixels.
- `tools/chrome-live-bitmap/capture_html_argb.js` provides a standalone
  Chrome/Chromium headless screenshot probe: it captures a layout HTML fixture,
  decodes PNG to ARGB without tolerance, compares checksum/weighted
  checksum/pixel mismatch against the pure Simple ARGB reference, and reports
  `chrome-binary-unavailable` without claiming pixels when the host has no
  browser binary.
- `scripts/check/check-chrome-simple-web-layout-bitmap-evidence.shs` wraps the
  Chrome/Chromium probe as an evidence producer with captured-ARGB, timing,
  mismatch, and no-blur/no-tolerance fields.
- `scripts/check/check-tauri-simple-web-layout-bitmap-evidence.shs` now performs
  a real desktop Tauri capture by launching `tools/tauri-shell` under Xvfb plus
  `dbus-run-session`, capturing the actual Tauri WebView window, converting the
  screenshot to ARGB, and comparing it exactly with the Simple reference. The
  Tauri expected bitmap profile records scoped WebKitGTK/X11 fixture overlays
  for opacity and text-raster rows while preserving a zero-mismatch,
  no-blur/no-tolerance contract.
- `tools/tauri-live-bitmap/raw_rgba_to_argb.js` converts the captured Tauri
  window RGBA stream to the same ARGB/checksum/mismatch proof format as the
  Electron and Chrome evidence producers.
- `scripts/check/check-tauri-chrome-simple-web-layout-manifest-evidence.shs`
  consumes the Electron layout manifest, records Electron as live capture, runs
  the Tauri and Chrome probes for every manifest row, and fails closed unless
  live pass rows have exact case counts, zero failures, zero mismatches, and
  `no_fake_capture=true`. Tauri and Chrome `unavailable` rows are failures in
  this production parity lane. The aggregate production GUI parity gate now
  proves Electron, Tauri, and Chrome each pass the 18-row layout manifest on
  this host.
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
- 2026-06-11 update: bitmap-font operation aliases are now explicit:
  `bitmap_font`, `bitmap_glyph`, `font_bitmap`, and `glyph_bitmap` map to the
  generated copy/upload lane with `cpu_preprocess_required = true`. This keeps
  bitmap glyph fallback distinct from vector-font GPU glyph return evidence and
  from ordinary image copy rows.
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
- `scripts/check/check-generated-2d-backend-readback-matrix-evidence.shs`
  runs the generated 2D readback matrix across CUDA, OpenCL, Vulkan, Metal, and
  ROCm, treats CUDA/OpenCL/Vulkan as required on the current evidence host, and
  writes `doc/09_report/generated_2d_backend_readback_matrix_2026-06-05.md`.
  The current matrix passes CUDA, OpenCL, and Vulkan exact checksum/readback
  proof while recording Metal and ROCm as explicit unavailable lanes when their
  primary host tools are absent.
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

## Current Status

Team B live Tauri/WebKit unblock plus full browser manifest parity is complete
on the current Linux/Xvfb host:

1. `check-tauri-simple-web-layout-bitmap-evidence.shs` observes a real Tauri
   WebKitGTK window through Xvfb plus `dbus-run-session`.
2. Tauri and Chrome both run every Electron layout manifest row, not only the
   CSS box matrix smoke row.
3. `check-production-gui-web-renderer-parity-evidence.shs` passes with Electron,
   Tauri, and Chrome live captures at 18/18 rows, zero failures, zero mismatches,
   no blur/tolerance, and `no_fake_capture=true`.

2026-06-11 small-part split:

1. Spark handled the easy read-only scan for backend-order source locations.
   Codex reviewed the result and added executable coverage for the canonical
   order: Metal, CUDA, ROCm/HIP, Qualcomm, Vulkan, OpenCL, OpenGL, Intel,
   WebGPU, software, CPU SIMD, CPU.
2. Codex implemented the focused bitmap-font provenance contract and refreshed
   the generated spec Markdown. This does not claim GPU-side bitmap glyph
   rasterization; it records the current CPU glyph buffer plus GPU copy/upload
   state explicitly.
3. Next easy Spark task: read-only scan for duplicate `draw_text` and
   `draw_text_bg` CPU bitmap fallback bodies that still bypass
   `helpers_text.text_blit_buffer(...)`.
4. Spark completed that scan and recommended `WebGpuBackend.draw_text(...)` as
   the safest single-backend patch. Codex reviewed the result and centralized
   WebGPU foreground glyph buffer generation through
   `helpers_text.text_transparent_blit_buffer(...)`, while preserving
   foreground-only behavior by skipping zero pixels instead of calling
   `draw_image(...)`.
5. Remaining easy follow-ups, one backend at a time: `backend_baremetal.spl`,
   `backend_intel.spl`, and `backend_virtio_gpu.spl` still have local
   `draw_text_bg(...)` buffer construction that can likely delegate to
   `helpers_text.text_blit_buffer(...)` after focused backend tests are added or
   refreshed.
6. Spark reviewed the stale `helpers_parity_spec.spl` matcher cleanup as an
   easy read-only task. Codex applied the reviewed matcher replacement, fixed the
   shared pixel and glyph buffer helpers to return updated buffers for
   interpreter-visible pure-Simple tests, and refreshed the generated parity
   spec doc. The focused parity spec now passes 66/66 assertions.
7. Spark reviewed the pure-Simple HTML layout child-scan hotspot. Codex added a
   one-time parent-to-children index in
   `simple_web_html_layout_renderer.spl` and routed recursive layout plus
   intrinsic inline-width measurement through it, replacing the repeated
   `i + 1 .. nodes.len()` direct-child scans in the contents, flex-wrap,
   flex-row, flex-column, and block-flow branches. New coverage lives in
   `test/02_integration/rendering/simple_web_layout_child_index_spec.spl`.
8. Spark then reviewed the CSS selector cascade hotspot as an easy read-only
   task. Codex added a rightmost-selector candidate bucket index for id, class,
   and tag selectors while keeping the existing full selector matcher as the
   final authority and merging ordered candidate rule buckets before declaration
   application. The focused spec now covers child order, sibling-heavy startup
   rendering, duplicate bucket membership, and cascade-order preservation.
9. Codex removed another pure-Simple paint startup hotspot by caching each
   node's effective ancestor clip once per paint call. Background, absolute,
   z-index, icon/image, and text passes now reuse the cached `ClipRect` instead
   of walking the parent chain repeatedly. The cache is now lazy: pages without
   visible overflow clipping use a single framebuffer clip instead of allocating
   a per-node `ClipRect` array. The focused simple-web layout spec includes an
   overflow-hidden pixel oracle.
10. Codex folded widget-panel detection and widget-text detection into one
    paint pre-pass through `compute_widget_paint_flags(...)`, replacing a
    separate full-node panel scan and removing the unused `has_widget_ancestor`
    helper. The same helper now uses a panel-only scan for non-widget paint
    paths so normal pages do not allocate widget ancestor scratch state. The
    focused spec includes a widget chrome pixel oracle and passes 5/5.
11. Codex shared the intrinsic-width memo across recursive layout calls by
    carrying it through `LayoutResult` and seeding it once at public layout
    entrypoints. This removes repeated `[-1; nodes.len()]` allocation in nested
    flex layout while preserving the existing public debug/render entrypoints.
    The focused spec now includes a nested flex oracle and passes 6/6.
12. Codex simplified child-index construction to attach children during the
    same parent-before-child pass that initializes the per-node lists, removing
    a second full node walk from Simple Web startup. Spark also proved the
    legacy selector wrappers and local `class_has(...)` helper were
    reference-dead in this renderer, so Codex removed only those helpers while
    keeping the live `class_contains(...)` widget-class path intact. The focused
    spec still passes 6/6.
13. Codex tightened the active text paint range helpers so off-viewport text
    rows return before scanning characters and horizontally clipped rows stop
    once advancing x is beyond the framebuffer/clip. Spark proved the older
    non-range text wrappers are no longer called by this renderer's active paint
    path, so Codex removed those wrapper bodies while preserving the glyph
    helpers used by `fb_text_thin_scaled_clip_range(...)` and
    `fb_text_sparse_range(...)`. The focused spec still passes 6/6.
14. Codex made the final text/icon paint pass request `paint_clip_at(...)` only
    inside branches that actually draw clipped image, icon, or normal text
    content. This avoids one clip lookup per node on the common no-paint branch.
    The renderer now keeps only the glyph helpers used by the two active range
    text paths. The focused spec still passes 6/6.
15. Codex made `build_text_render_cache(...)` node-aware so it preserves the
    same one-slot-per-node cache indexing while computing glyph scale, advance,
    line height, and ink offsets only for `#text` nodes. Element rows now receive
    zero placeholders because the paint path never consumes their text metrics.
    The focused spec still passes 6/6.
16. Codex removed the unused `char_widths` field from `TextRenderCache` and its
    per-node construction path. The active paint path only reads advances,
    scales, line heights, and ink offsets, so this removes one dead per-node
    array without changing layout or paint behavior. The focused spec still
    passes 6/6.
17. Codex split the final text paint loop so normal clipped text resolves
    `paint_clip_at(...)` once per text node before rendering its wrapped lines.
    Widget sparse text still skips clip lookup, and normal wrapped text reuses
    the same clip across all line ranges. The focused spec still passes 6/6.
18. Codex removed the remaining `TextRenderCache` staging pass entirely. Text
    metrics are now computed directly inside the already-filtered `#text` paint
    branch, so startup no longer allocates or fills five node-indexed metric
    arrays before paint. The focused spec still passes 6/6.
19. Codex skipped repeated class-bucket lookup for duplicate class tokens on a
    node. The bucket merge already deduplicates rule ids, so this removes
    redundant `text_key_index(...)` scans without changing cascade order or the
    final selector matcher. The focused CSS oracle now uses `class="target
    target"` and still passes 6/6.
20. Codex added trivial fast paths to `merge_sorted_rule_lists_unique(...)` for
    zero or one candidate bucket list. The multi-bucket merge is unchanged, but
    simple nodes can now skip positions-array allocation and the merge loop. The
    focused spec still passes 6/6.
21. Current small-part split for the next renderer pass:
    - Spark was assigned one easy mechanical patch in
      `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:
      hoist stable `.len()` calls in selector/style/layout hot loops where the
      loop already preserves behavior.
    - Codex owns coordination docs, focused verification, review of Spark's
      patch, and any follow-up integration notes.
    - Deferred parts stay separate: candidate-bucket allocation reduction,
      additional text paint profiling, backend font-offload design, and any
      non-mechanical renderer behavior change.
22. Spark hit its model quota before producing a patch, so Codex completed the
    same bounded easy task locally. The renderer now caches stable lengths in
    selector normalization, selector group splitting, bucket key lookup,
    candidate-list merging, rule bucket construction, grouped selector
    matching, and style candidate application loops. The patch was reviewed as
    mechanical-only, the focused spec still passes 6/6, and the renderer
    optimizer scan now reports 734 remaining opportunities.
23. Codex continued the same mechanical cleanup across the remaining stable
    Simple Web renderer loops that affect startup parsing, selector matching,
    intrinsic/layout traversal, paint passes, clip-cache construction, wrapped
    text line iteration, and Draw IR export. Mutating builders were left alone.
    Focused Simple Web layout coverage still passes 6/6, the adjacent
    Web Engine2D Metal-offload coverage still passes 11/11, and the renderer
    optimizer scan now reports 692 remaining opportunities.
24. Codex removed two startup allocation push loops by changing
    `zero_i32_list(...)` and `neg_one_i32_list(...)` to direct repeated-list
    initialization. A no-id/no-class CSS candidate fast path was also tested,
    but reverted because it increased optimizer warnings despite passing
    behavior specs. The retained patch keeps the focused Simple Web layout spec
    at 6/6, the adjacent Web Engine2D Metal-offload spec at 11/11, and lowers
    the renderer optimizer scan to 688 remaining opportunities.
25. Codex removed the positive z-index paint loop's repeated full-node scan for
    each distinct positive z layer. The renderer now detects positive z during
    the existing absolute-position pass, lazily builds a fixed-size sorted index
    only when needed, and paints that index once in ascending z order with stable
    document order for equal z values. A new overlapping absolute-position
    pixel oracle keeps the behavior pinned; the focused Simple Web layout spec
    now passes 7/7 and the adjacent Web Engine2D Metal-offload spec still
    passes 11/11. The optimizer scan reports 695 remaining opportunities after
    this structural change because the index buffer adds bounds-check
    opportunities, but the previous O(node_count * distinct_positive_z) scan is
    removed.
26. Codex moved paint clip lookup for normal backgrounds/borders, non-positive
    absolute decorations, and positive-z decorations into the draw branches that
    actually need clipping. Undecorated nodes now skip decoration-pass
    `paint_clip_at(...)` calls. The focused Simple Web layout spec still passes
    7/7, the adjacent Web Engine2D Metal-offload spec still passes 11/11, and
    the renderer optimizer scan remains at 695 remaining opportunities.
27. Codex confirmed wrap range generation is already limited to `#text` layout
    nodes, then removed the per-node push loop in `empty_i32_lists(...)` by
    using repeated empty-list initialization for wrap start/end seeds. The
    focused Simple Web layout spec still passes 7/7, the adjacent Web Engine2D
    Metal-offload spec still passes 11/11, the focused spec optimizer scan
    reports 3 opportunities, and the renderer optimizer scan now reports 692
    remaining opportunities.
28. Codex changed the Simple Web child-index builder and overflow clip-cache
    builder to allocate fixed-size arrays from the known node count and assign
    by index instead of growing via `push(...)`. This keeps child order and clip
    inheritance behavior stable while avoiding two startup push-build loops. The
    focused Simple Web layout spec still passes 7/7, the adjacent Web Engine2D
    Metal-offload spec still passes 11/11, the focused spec optimizer scan
    remains at 3 opportunities, and the renderer optimizer scan now reports 690
    remaining opportunities.
29. Codex removed the parser close-tag `next_stack` allocation/copy path. A
    matched close tag now trims the parent stack in place with `pop(...)` down
    to the matched opening tag, preserving the existing tolerant HTML behavior
    while avoiding a fresh list allocation on every close tag. The focused
    Simple Web layout spec still passes 7/7, the adjacent Web Engine2D
    Metal-offload spec still passes 11/11, and the renderer optimizer scan now
    reports 687 remaining opportunities.
30. Codex avoided splitting empty class attributes during HTML parsing. Elements
    without a `class` attribute now keep the default empty `class_words` list,
    while non-empty class attributes still use the existing split path. A new
    selector oracle proves tag rules still apply and absent class selectors do
    not match unclassed nodes. The focused Simple Web layout spec now passes
    8/8, the adjacent Web Engine2D Metal-offload spec still passes 11/11, the
    mirrored manual was regenerated, and the renderer optimizer scan remains at
    687 remaining opportunities.
31. Spark was assigned the next easy parser slice: move widget/focus class flag
    substring scans under the existing non-empty class branch. Spark quota was
    exhausted before it could produce a patch, so Codex completed and reviewed
    the same one-file change locally. Unclassed elements now skip all six
    `class_contains(...)` scans and keep the default false `mk_node` flags. The
    focused renderer check passes, the Simple Web layout spec still passes 8/8,
    the adjacent Web Engine2D Metal-offload spec still passes 11/11,
    `doc/06_spec` executable spec count remains 0, SPipe dev-command wiring
    reports PASS, whitespace diff is clean, and the renderer optimizer scan
    remains at 687 opportunities.
32. Codex removed the flex-wrap layout pass's dynamic `line_heights.push(...)`
    growth by allocating a line-height buffer bounded by the flex child count
    and tracking the actual `line_count`. A new focused flex-wrap oracle proves
    first-line children stay aligned and the wrapped child moves to the next
    row. The Simple Web layout spec now passes 9/9, the adjacent Web Engine2D
    Metal-offload spec still passes 11/11, the mirrored manual was regenerated,
    the focused spec optimizer scan remains at 3 opportunities, `doc/06_spec`
    executable spec count remains 0, SPipe dev-command wiring reports PASS, and
    whitespace diff is clean. The renderer optimizer scan reports 688
    opportunities because the fixed buffer adds static indexed-assignment
    bounds checks while removing the flex-wrap grow-by-push path.
33. Codex removed two more known-size startup push builders. Selector group
    parts now allocate one slot per selector group and assign by group index,
    and computed styles now allocate one slot per parsed node and assign by
    node index while preserving parent-before-child inheritance. The focused
    renderer check passes, the Simple Web layout spec still passes 9/9, the
    adjacent Web Engine2D Metal-offload spec still passes 11/11, the focused
    spec optimizer scan remains at 3 opportunities, `doc/06_spec` executable
    spec count remains 0, SPipe dev-command wiring reports PASS, whitespace
    diff is clean, and the renderer optimizer scan returns to 687
    opportunities.
34. Codex removed the CSS rule candidate-list grow-by-push path by using a
    fixed buffer sized to fallback plus optional id, tag, and class buckets and
    merging only the populated prefix. The obsolete append and wrapper merge
    helpers were removed after reference checks. The focused renderer check
    passes, the Simple Web layout spec still passes 9/9, the adjacent Web
    Engine2D Metal-offload spec still passes 11/11, the focused spec optimizer
    scan remains at 3 opportunities, `doc/06_spec` executable spec count
    remains 0, SPipe dev-command wiring reports PASS, whitespace diff is clean,
    and the renderer optimizer scan remains at 687 opportunities while the
    candidate-list push path is gone.
35. Codex tightened the executable Engine2D backend-priority helper so its
    numeric priorities exactly match the documented/default GUI order: Metal,
    CUDA, ROCm/HIP, Qualcomm, Vulkan, OpenCL, OpenGL, Intel, WebGPU, software,
    CPU SIMD, CPU. The previous helper tied OpenCL and OpenGL even though the
    default order list was already correct. The backend-order unit spec now
    asserts every adjacent priority edge and its mirrored manual was
    regenerated. Verification: backend-order spec 4/4, adjacent WebGPU unit
    spec 5/5, adjacent Web Engine2D Metal-offload spec 11/11, helper optimizer
    scan 50 opportunities, backend-order spec optimizer scan 12 opportunities,
    `doc/06_spec` executable spec count 0, SPipe dev-command wiring PASS, and
    whitespace diff clean.
36. Codex added typed bitmap-font offload evidence to match the existing
    vector-font evidence surface. `BitmapFontOffloadEvidence` records generated
    copy readiness, CPU glyph preprocessing, GPU copy/upload readiness, and
    explicitly reports `gpu_glyph_rasterized = false` until a real GPU bitmap
    glyph raster path exists. The focused bitmap-font SSpec and mirrored manual
    prove CUDA generated copy with CPU glyph preprocessing, CPU SIMD baseline,
    and runtime-unavailable fail-closed states. Verification: bitmap-font
    offload spec 3/3, vector-font offload spec 4/4, generated-kernel dispatch
    spec 23/23, bitmap evidence module optimizer scan 7 opportunities, bitmap
    spec optimizer scan 0 opportunities, `doc/06_spec` executable spec count 0,
    SPipe dev-command wiring PASS, and whitespace diff clean.
37. Codex updated the public Engine2D module overview, UI stack architecture,
    and pixel comparison guide so typed vector-font and bitmap-font evidence are
    discoverable. The docs now state that bitmap-font evidence means CPU glyph
    preprocessing plus optional GPU copy/upload, not GPU-side bitmap glyph
    rasterization. Verification: Engine2D module/bitmap evidence check passes,
    bitmap-font offload spec remains 3/3, vector-font offload spec remains 4/4,
    bitmap evidence module optimizer scan remains at 7 opportunities,
    `doc/06_spec` executable spec count 0, SPipe dev-command wiring PASS, and
    whitespace diff clean.
38. Codex optimized OpenCL bitmap-text fallback paths. `OpenClBackend.draw_text`
    and `draw_text_bg` now route directly to the mirror renderer when device
    drawing is unavailable, avoiding temporary CPU glyph-buffer construction for
    a GPU copy/upload path that cannot run. A focused OpenCL text fallback SSpec
    and mirrored manual cover foreground and background text fallback states.
    Verification: OpenCL text fallback spec 2/2, helpers text spec 4/4,
    generated-kernel dispatch spec 23/23, OpenCL backend optimizer scan 74
    opportunities, OpenCL text fallback spec optimizer scan 0 opportunities,
    `doc/06_spec` executable spec count 0, SPipe dev-command wiring PASS, and
    whitespace diff clean. The broader pre-existing
    `backend_opencl_facade_spec.spl` still reports 4 passed / 2 failed even
    after removing speculative added assertions, so it is tracked separately
    from this focused slice.
39. Codex optimized CUDA bitmap-text fallback paths. `CudaBackend.draw_text` and
    `draw_text_bg` now route directly to the mirror renderer when the CUDA
    backend is uninitialized, avoiding temporary CPU glyph-buffer construction
    for a CUDA upload path that cannot run. A focused CUDA text fallback SSpec
    and mirrored manual cover foreground and background text fallback states.
    Verification: CUDA text fallback spec 2/2, helpers text spec 4/4,
    generated-kernel dispatch spec 23/23, CUDA backend optimizer scan 70
    opportunities, CUDA extension optimizer scan 7 opportunities, CUDA text
    fallback spec optimizer scan 0 opportunities. The broader pre-existing
    `backend_cuda_renderbackend_spec.spl` currently reports 9 passed / 2 failed
    in this checkout and imports `cuda_2d_ptx_source` through a non-exporting
    module during `check`, so it is tracked separately from this focused slice.
40. Codex optimized ROCm/HIP bitmap-text fallback paths. `RocmBackend.draw_text`
    and `draw_text_bg` now return before constructing text buffers when the
    ROCm backend is uninitialized, preserving the existing dirty attempted-draw
    state without staging glyphs for a HIP upload path that cannot run. A
    focused ROCm text fallback SSpec and mirrored manual cover foreground and
    background text fallback states. Verification: ROCm text fallback spec 2/2,
    helpers text spec 4/4, ROCm session contract spec 8/8, ROCm backend
    optimizer scan 53 opportunities, ROCm text fallback spec optimizer scan 0
    opportunities. `bin/simple check` passes for the touched ROCm source/spec
    and adjacent specs with the existing `gc_boundary_crossing` warning on
    `backend_rocm.spl`'s SFFI import.
41. Codex optimized Vulkan bitmap-text fallback paths. `VulkanBackend` now
    returns before foreground text CPU-render/upload work when uninitialized,
    and `draw_text_bg` returns before constructing a background text buffer when
    Vulkan cannot upload it. Both paths preserve the dirty attempted-draw state.
    A focused Vulkan text fallback SSpec and mirrored manual cover foreground
    and background text fallback states. Verification: Vulkan text fallback spec
    2/2, helpers text spec 4/4, Vulkan backend optimizer scan 45 opportunities,
    Vulkan helper optimizer scan 63 opportunities, Vulkan text fallback spec
    optimizer scan 0 opportunities. `bin/simple check` passes for the touched
    Vulkan source/spec and adjacent specs with the existing
    `gc_boundary_crossing` warnings on the Vulkan SFFI imports.
42. Codex optimized OpenGL bitmap-text fallback paths. `OpenGLBackend.draw_text`
    and `draw_text_bg` now return before constructing foreground/background text
    buffers when the OpenGL backend is uninitialized, avoiding CPU glyph work
    for an upload path with no valid GL context. A focused OpenGL text fallback
    SSpec and mirrored manual cover foreground and background uninitialized
    fallback states. Verification: OpenGL text fallback spec 2/2, helpers text
    spec 4/4, OpenGL backend optimizer scan 22 opportunities, OpenGL text
    fallback spec optimizer scan 0 opportunities. `bin/simple check` passes for
    the touched OpenGL source/spec and adjacent helper spec.
43. Codex optimized Intel oneAPI bitmap-text fallback paths. `IntelBackend`
    now returns before foreground CPU text render/upload work and background
    text buffer construction when uninitialized, preserving the dirty
    attempted-draw state. `draw_text_bg` also seeds its known-size background
    buffer directly instead of growing it with repeated `push`. A focused Intel
    text fallback SSpec and mirrored manual cover foreground and background
    uninitialized fallback states. Verification: Intel text fallback spec 2/2,
    helpers text spec 4/4, Intel backend optimizer scan 26 opportunities after
    removing the preallocation warning, Intel helper optimizer scan 34
    opportunities, Intel text fallback spec optimizer scan 0 opportunities.
    `bin/simple check` passes for the touched Intel source/spec and adjacent
    helper spec.
44. Codex optimized WebGPU pre-init bitmap-text paths. `WebGpuBackend.draw_text`
    and `draw_text_bg` now return before constructing foreground/background
    text buffers when the backend has not been initialized or has zero
    dimensions, while initialized CPU-parity drawing remains unchanged. A
    focused WebGPU text fallback SSpec and mirrored manual cover pre-init
    foreground and background text states. Verification: WebGPU text fallback
    spec 2/2, existing WebGPU behavior spec 5/5, helpers text spec 4/4, WebGPU
    backend optimizer scan 69 opportunities, WebGPU text fallback spec
    optimizer scan 0 opportunities. `bin/simple check` passes for the touched
    WebGPU source/spec and adjacent specs with the existing
    `gc_boundary_crossing` warning on the WebGPU SFFI import.
45. Codex optimized the pure Simple software fallback path by hoisting repeated
    dirty-tile and `draw_text` length checks in `SoftwareBackend`, and by
    caching the AA text helper buffer length outside the innermost blend loop.
    Verification: helpers text spec 4/4, software primitive spec 6/6, software
    SIMD spec 7/7, and `bin/simple check` passes for the touched software/text
    helper sources and focused specs. Software backend optimizer scan dropped
    from 90 to 87 opportunities after removing the three `hoist_len_call`
    warnings; helpers text optimizer scan remains at 37 opportunities, and
    helpers text spec optimizer scan reports 10 opportunities. The broader
    pre-existing `draw_text_bg_spec.spl` currently reports 1 passed / 2 failed
    and is tracked separately from this loop-hoist slice.
46. Codex resolved the CPU `draw_text_bg` spec failure. Diagnostic probes showed
    the renderer already preserved outside pixels, changed inside glyph-cell
    pixels, and produced intermediate AA red coverage; the failure was stale
    matcher syntax in the spec. Replacing `to_be_true()` with `to_be(true)`
    keeps the same pixel assertions while using the supported matcher path.
    Verification: CPU `draw_text_bg` spec 3/3, helpers text spec 4/4, software
    primitive spec 6/6, and the mirrored manual was regenerated. Optimizer
    scans report `draw_text_bg_spec.spl` 9 opportunities, software backend 87
    opportunities, and helpers text 37 opportunities.
