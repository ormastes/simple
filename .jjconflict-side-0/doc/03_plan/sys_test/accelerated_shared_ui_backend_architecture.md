<!-- codex-design -->
# Accelerated Shared UI Backend Architecture - System Test Plan

Date: 2026-06-03
Status: Candidate plan pending requirement selection

## Test Surfaces

- Shared semantic UI: TUI, pure Simple web, Electron, Tauri, and NodeJS/browser
  adapters should expose the same widget tree and command outcomes for one
  canonical app fixture.
- Render pipeline: pure Simple web renderer must feed Engine2D capture/equality
  for a canonical 2D scene.
- GPU offload: CUDA and OpenCL generated kernels must share the same logical
  operation and report separate artifact/runtime/readback evidence.
- Backend comparison: pure Simple, Tauri, Electron, NodeJS/browser, CPU
  scalar/SIMD, CUDA, OpenCL, Vulkan, Metal, and WebGPU should emit normalized
  performance samples where available.

## Planned Specs

- `test/03_system/app/ui/feature/accelerated_shared_ui_semantic_contract_spec.spl`
  covers semantic tree and command parity across shell adapters.
- `test/03_system/app/ui/feature/accelerated_shared_render_pipeline_spec.spl`
  covers pure Simple web renderer to Engine2D capture/equality.
- `test/03_system/app/compiler/feature/cuda_opencl_offload_contract_spec.spl`
  covers tagged GPU target selection, diagnostics, and artifact metadata.
- `test/05_perf/backend_compare/accelerated_backend_comparison_spec.spl`
  covers normalized benchmark sample parsing and unavailable-state reporting.

## Evidence Requirements

- TUI captures under `build/test-artifacts/...`.
- GUI/browser screenshots or pixel outputs under `doc/06_spec/image/...`.
- API/protocol captures for Electron/Tauri/NodeJS envelopes.
- Perf reports under `doc/09_report/...` with `BackendComparisonSample` rows.
- Generated manuals under mirrored `doc/06_spec/...` paths.

## Quality Gates

- No placeholder passes, empty specs, or `expect(true).to_equal(true)`.
- Every backend fallback must preserve the preferred backend and reason.
- Hardware-unavailable is not a graphical pass.
- Readback or checksum evidence is required before reporting device execution.
- `find doc/06_spec -name '*_spec.spl' | wc -l` must return `0`.
