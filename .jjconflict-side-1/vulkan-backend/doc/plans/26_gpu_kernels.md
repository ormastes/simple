# Plan 26: GPU Kernels (`#[gpu]`) and SPIR-V Codegen

## Goal
Implement Feature 126: compile functions annotated with `#[gpu]` into GPU kernels, targeting SPIR-V first, with a clean separation between host and device code paths.

## Scope
- Attribute parsing and validation for `#[gpu]` on functions.
- Restricted kernel subset (no GC, no dynamic allocation, limited control flow).
- SPIR-V IR lowering and module emission.
- Host-side launch API and runtime plumbing (buffer upload, dispatch, download).

## Design Principles
- Keep kernel code pure and side-effect limited; reject unsupported features early in semantic analysis.
- Share type layout rules with existing codegen (types_util) to avoid ABI drift.
- Reuse module resolution and packaging; kernels live alongside normal modules but compile through a GPU pipeline.

## Workplan
1) Frontend and validation
   - Parser: recognize `#[gpu]` attribute on functions; extend AST metadata.
   - Semantic checks: enforce kernel subset (no actors/async/gc/strings/dicts; allow numeric arrays, POD structs, simple loops).
   - Type rules: ensure kernel params are device-compatible (scalars, vectors, buffers, POD structs).

2) IR and lowering
   - Add GPU-targeted MIR/IR pass or flag: mark `#[gpu]` functions and strip unsupported instructions.
   - Introduce a minimal SPIR-V builder (module, types, functions, basic blocks) or integrate an existing crate if available.
   - Lower MIR ops used in kernels to SPIR-V: arithmetic, comparisons, loads/stores, control flow, builtin intrinsics (workgroup/local ids).

3) Runtime/host API
   - Define host-side API for launching kernels: `gpu::launch(kernel, grid, block, args)` with buffer handle types.
   - Implement buffer abstractions (device buffer, host-to-device copy, device-to-host copy).
   - Provide a fallback stub/runtime error on platforms without GPU backend compiled in.

4) Build and integration
   - Feature flag the GPU backend (`gpu` or `gpu-spirv`) so builds without Vulkan/spirv-tools still succeed.
   - Emit SPIR-V binaries into the build output (or inline into SMF metadata) and expose them to the runtime.
   - Extend the package/loader to carry kernel blobs alongside CPU code (metadata in SMF section).

5) Testing
   - Unit: SPIR-V builder sanity (type IDs, instruction encoding), lowering of basic ops.
   - Integration (CPU-only): compile kernels and inspect emitted SPIR-V (golden tests).
   - Optional device smoke tests (guarded): vector add kernel on Vulkan-capable hosts.

## Milestones and acceptance
- **M0: Frontend flag + validation** — `#[gpu]` parsed, invalid constructs rejected with diagnostics; unit tests for validator.
- **M1: SPIR-V builder** — Can build a trivial kernel (no ops) and encode SPIR-V; golden test on emitted bytes.
- **M2: Lowering core ops** — Arithmetic/control flow/loads-stores lowered; golden tests for vector-add and saxpy kernels.
- **M3: Host launch API** — `gpu::launch` available, buffer types implemented with stub backend; CPU-only tests exercise API shape.
- **M4: End-to-end (optional device)** — Guarded smoke test running a kernel on Vulkan if available; otherwise skip with clear message.

## Acceptance criteria
- `#[gpu]` functions are rejected when using unsupported features (GC, async, dynamic alloc, strings/dicts).
- SPIR-V modules pass `spirv-val` (when tooling is available).
- Host API compiles without GPU toolchain when feature flag is off (graceful stubs).
- SMF (or build artifacts) carry kernel blobs with metadata for launch dimensions and parameter layouts.

## Risks
- Toolchain availability (spirv-tools, Vulkan SDK); mitigate with feature flags and clear errors.
- ABI/layout mismatches between host and device; mitigate by reusing shared type layout helpers.
- Kernel subset creep; keep validator strict and document supported operations.
