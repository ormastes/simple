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

## Integration Order

1. Team A and Team B establish the UI/render contract path.
2. Team C proves OpenCL runtime states and typed evidence.
3. Team D extends offload validation and metadata once runtime states are real.
4. Team E normalizes evidence after Teams A-C expose stable report fields.
5. Run release-blocking verification only after all generated specs are under
   `doc/06_spec/**/*.md` and `find doc/06_spec -name '*_spec.spl' | wc -l`
   returns `0`.

## Current Next Slice

The next smallest implementation slice is Team A plus a narrow Team B fixture:

1. Inspect `src/lib/common/ui/semantic_contract.spl` and `web_render_api.spl`.
2. Add one shared fixture adapter if any surface lacks a helper.
3. Add one spec that compares semantic command results across Web, TUI,
   Electron, Tauri, and headless helpers.
4. Add one render artifact field that records whether Engine2D was reached,
   then assert the field in the pure Simple web renderer fixture.
