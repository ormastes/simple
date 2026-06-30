<!-- codex-research -->
# Accelerated Shared UI Backend Architecture - Local Research

Date: 2026-06-03

## Scope

This research maps the active objective across UI, web renderer, Engine2D,
compiler GPU codegen, OpenCL, SIMD, and performance evidence. It builds on the
existing shared-WM completion audit instead of replacing it.

## Current Evidence

- `doc/03_plan/shared_wm_renderer_unification_completion_audit.md` reports the
  Web/Electron/Tauri/pure Simple web render API slice as complete for the
  current contract. It also reports CPU, CUDA, and Metal Engine2D renderers as
  sharing `std.gpu.engine2d.backend.RenderBackend`.
- `doc/04_architecture/ui/shared_ui_contract.md` is narrower than the active
  objective: it treats native TUI, Electron, and Tauri as adapter-only for the
  shared test API. A future version must promote those surfaces behind a shared
  semantic UI interface rather than only a shared web-render envelope.
- `src/app/ui/` already has backend entrypoints for browser, CLI, Electron,
  headless, render, Tauri, TUI, TUI-web, and web. `src/app/ui.web/`,
  `src/app/ui.electron/`, and `src/app/ui.tauri/` provide concrete adapters.
- `src/lib/gc_async_mut/gpu/browser_engine/` contains the pure Simple browser
  engine and Simple-web renderer family. `simple_web_engine2d_renderer.spl` and
  `backend_screenshot_capture.spl` connect renderer output to Engine2D/capture
  evidence.
- `src/lib/gc_async_mut/gpu/engine2d/backend.spl` defines the shared Engine2D
  backend family. CPU, CUDA, Vulkan, Metal, WebGPU, ROCm, Intel, and OpenCL
  session or backend files exist under `engine2d/`.
- `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl` already contains an
  OpenCL ICD-style session boundary with platform/context/queue/program/kernel
  state and generated 2D kernel launch methods.
- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_opencl.spl` and
  `src/runtime/runtime_simd_dispatch.c` are the lower-level OpenCL runtime
  hook candidates. Current explorer evidence found only `clGetPlatformIDs`
  wired; context, queue, program build, kernel creation, enqueue, and finish are
  still stub-like and must be made real before OpenCL can match CUDA.
- `src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl` already
  includes `opencl` launch plans, SPIR-V artifact names, and an OpenCL execution
  request shape. This is planning/runtime evidence, not proof that the compiler
  can emit OpenCL-ready kernels end to end.
- `src/compiler_rust/compiler/src/codegen/llvm/gpu.rs` is CUDA/NVPTX-specific.
  It initializes and emits NVPTX/PTX and has no parallel OpenCL/SPIR-V target
  backend.
- `src/compiler_rust/runtime/src/cuda_runtime.rs` is the CUDA-side reference for
  a real runtime bridge: Driver API loading, PTX module load, kernel lookup,
  launch, memory operations, and typed fallback stubs. OpenCL needs an
  equivalent bridge or a complete C-runtime ICD implementation.
- `src/compiler/35.semantics/gpu_checker.spl` validates the GPU kernel subset
  for `@gpu`, `@gpu_kernel`, and `kernel fn`, but does not yet distinguish CUDA
  vs OpenCL feature availability or address-space rules.
- `doc/02_requirements/feature/graphics_backend_acceleration_options.md` and
  `doc/02_requirements/nfr/graphics_backend_acceleration_options.md` already
  define performance-first backend options, but they under-specify OpenCL.
- Existing performance infrastructure is split by concern:
  `scripts/check/check-startup-size-performance-audit.shs` measures stripped startup
  probes, binary size, section bytes, loaded libraries, and average runtime;
  `scripts/check/check-web-baremetal-size-audit.shs` measures web/bare-metal size
  budgets; `test/05_perf/graphics_2d/` contains C, Vulkan, CUDA SFFI, Metal, and
  tiered-JIT 2D benchmark files; `test/05_perf/tauri_equiv/` records GUI/Tauri
  workflow fields but currently uses simulated values.

## Local Gaps

1. Shared UI semantics still need a contract layer above surface transports:
   native TUI, GUI, web, Electron, and Tauri must map to the same semantic
   widget tree, command, event, capture, and accessibility state model.
2. OpenCL is present as an Engine2D runtime/session concept, but compiler
   emission is still CUDA/NVPTX-centric.
   It is also not yet runtime-equivalent to CUDA because the OpenCL SFFI and C
   dispatch layers do not perform full context/program/kernel/queue operations.
3. The tagged Simple offload model needs a backend-neutral artifact contract:
   tags select `cuda`, `opencl`, or `auto`, while the compiler emits PTX or
   OpenCL SPIR-V/OpenCL C with the same kernel ABI where possible.
4. Performance evidence must compare startup, binary size, latency, RSS, frame
   time, readback, and fallback status across pure Simple, Tauri, Electron,
   NodeJS, CPU SIMD, CUDA, OpenCL, Vulkan, Metal, and WebGPU.
   Current evidence is fragmented: Electron/Node scripts are mostly pixel
   oriented, Tauri is pending/simulated, GPU benchmarks report different fields,
   and RSS is not consistently captured.
5. OpenCL readiness must separate three states: API/runtime unavailable,
   compiler artifact unavailable, and device execution/readback mismatch.

## Candidate Feature Name

Use `accelerated_shared_ui_backend_architecture` for the umbrella planning
track. Keep `graphical_backend_equality` as the narrow first slice and
`graphics_backend_acceleration` as the acceleration requirement option family.
