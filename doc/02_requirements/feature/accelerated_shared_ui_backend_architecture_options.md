<!-- codex-research -->
# Accelerated Shared UI Backend Architecture - Feature Options

Date: 2026-06-03

## Option A: Documented Adapter Unification

Description: keep current implementations intact, update contracts so TUI, GUI,
web, Electron, and Tauri are all described as adapters around shared semantic UI
and render artifacts.

Pros:
- Lowest risk and aligns with existing shared-WM work.
- Clarifies the architecture before more code moves.

Cons:
- Does not add OpenCL compiler emission.
- Does not prove performance or remove duplication.

Effort: M, 8-14 files.

## Option B: OpenCL Runtime Completion Slice

Description: extend existing Engine2D OpenCL session and SFFI proof so generated
2D kernels can be loaded, submitted, synchronized, and read back with typed
unavailable diagnostics.

Pros:
- Directly closes the largest runtime gap after CUDA.
- Reuses `opencl_session.spl` and `generated_kernel_dispatch.spl`.

Cons:
- Still depends on compiler-generated artifacts or checked-in fixtures.
- Requires host OpenCL ICD availability or high-quality unavailable evidence.

Effort: L, 16-28 files.

## Option C: Tagged Simple GPU Offload For CUDA And OpenCL

Description: define and implement backend-neutral Simple tags for offload, such
as `@gpu(target="cuda")`, `@gpu(target="opencl")`, and `@gpu(target="auto")`,
then emit PTX for CUDA and OpenCL SPIR-V/OpenCL C artifacts for OpenCL from the
same restricted kernel subset.

Pros:
- Matches the requested language-level offload model.
- Makes CUDA and OpenCL comparable at compiler, runtime, and evidence layers.
- Enables vector-font, image, compositing, and other 2D operations to move from
  handwritten backend code toward generated kernels.

Cons:
- Highest compiler risk.
- Needs target-environment validation and address-space mapping per backend.
- Requires careful compatibility with existing GPU checker behavior.

Effort: XL, 35-60 files.

## Option D: Full Accelerated UI Backend Capsule Refactor

Description: apply MDSOC capsules for `ui.semantic`, `ui.host`, `web.render`,
`engine2d.render`, `gpu.compute`, `compiler.offload`, and
`optimization.provider`, then move duplicated backend logic behind those
capsules.

Pros:
- Best long-term structure for pure Simple, Tauri, Electron, NodeJS, TUI, web,
  Engine2D, SIMD, CUDA, OpenCL, Vulkan, and Metal.
- Makes startup/bin-size/perf evidence part of the architecture.

Cons:
- Too broad to start without Options B/C evidence.
- High merge and verification cost.

Effort: XL, 60+ files.

## Recommended Selection

Select Option C if the next milestone is language-level CUDA/OpenCL offload.
Select Option B first if OpenCL runtime proof must land before compiler work.
