# Draft Requirements — Unified CPU/GPU Compute Stdlib (CCCL Parity)

**Status:** DRAFT (Research Step 1 output) · **Domain:** lib · **Date:** 2026-06-16
**Source research:** `doc/01_research/lib/gpu_containers_unified/gpu_containers_algorithms_stdlib_cuda_parity_2026-06-16.md`

## FR-1 — Unified container types (libcu++ parity)
Provide generic, CPU+GPU-usable container/utility types equal-or-better than CCCL libcu++:
`Array<T,N>`, `Span<T>`, `MdSpan<T>`, `InplaceVector<T,N>`, `Bitset<N>`, `Complex<T>`,
`Atomic<T>`, `Barrier`/`Latch`/`Semaphore`, bit ops, random engines/distributions.
**AC:** each type compiles and runs in interpreter, and is usable inside a `@gpu_kernel`
body for at least the CUDA backend.

## FR-2 — Generic algorithm surface (Thrust parity)
Provide generic algorithms over arbitrary `T`: `transform`, `for_each`, `reduce`,
`transform_reduce`, `inclusive_scan`, `exclusive_scan`, `sort`, `stable_sort`,
`sort_by_key`, `copy_if`, `remove_if`, `unique`, `partition`, `gather`, `scatter`,
`merge`, `find`, `binary_search`, `lower_bound`, `upper_bound`, `count`, `min_element`,
`max_element`, `reduce_by_key`.
**AC:** replaces the f32-only `gpu_*` stubs; each algorithm is generic and result-verified
against the CUDA oracle (FR-4).

## FR-3 — Single execution-policy switch (consistent + config-switchable)
One `ExecTarget { Auto, Cpu, CpuPar, Cuda, Vulkan, Metal, PureSimple }` resolved through a
**single** resolver that subsumes the four existing precedents (`SIMPLE_2D_BACKEND`,
`gpu_target_metadata` order, `@gpu_kernel(target:)`, BLAS provider).
**AC:** the same algorithm call runs on CPU or a GPU backend selected only by config/env;
`Auto` honors the landed `vulkan,metal,cuda,hip,opencl→cpu` preference order.

## FR-4 — CUDA-as-backend + implementation order
When `Cuda` is selected and `libcuda` is present, dispatch to CUDA (optionally Thrust/CUB
via FFI). Build order: **CUDA → pure-Simple → Vulkan → Metal**; CUDA cell is the reference
oracle.
**AC:** CUDA path verified on a CUDA host; absent-CUDA degrades per fail-closed policy.

## FR-5 — CUB-equivalent primitives
Expose block- and warp-level cooperative primitives (extend existing warp ops in
`gpu_intrinsics.spl` with block-level reduce/scan).
**AC:** block reduce/scan usable from a kernel and oracle-verified.

## Out of scope (this initiative)
CCCL surface that is not GPU-relevant (chrono timezones, ranges views) may be deferred —
"equal or better" need not copy CUDA's own omissions.
