# Feature: gpu_containers_unified

## Raw Request
> curent simple common algorithm and containers like cuda … both cpu/gpu, organize with
> existing gpu api set, consistent + switchable by config, impl cuda → pure simple → vulkan
> → metal, parallel agent teams + opus verification, find+fix bugs (incl perf).
> FOLLOW-UP (2026-06-16): two-level device-class target model (default/cpu/simd_cpu/gpu/
> fpga/simd) like SYCL device_type, NOT backend-API tags. Two backend DOMAINS (drawing vs
> processing). Config is `suggest` (soft) or `require` (hard/fail-closed).
> GOAL: use spipe dev skill, refactor ExecTarget, impl pure-simple lib for gpu+cpu and for
> cuda/metal/vulkan backed container/algorithm, consistent + config selectable, deep plan +
> parallel agent teams.

## Task Type
feature

## Refined Goal
Two-level config-selectable `ExecTarget` policy (L1 device class, L2 auto backend, suggest/
require) + a generic pure-Simple container & algorithm surface in `std.compute` that
dispatches through it, with cuda/metal/vulkan processing-backend routing (honest payload-
gated offload + CPU fallback), built via parallel agent teams and differential-verified.

## Acceptance Criteria  (status)
- AC-1 two-level ExecTarget, no class/backend conflation — **DONE** (exec_target.spl; 11/11).
- AC-2 single resolver subsumes env/order/kernel selectors, suggest vs require fail-closed —
  **DONE** (resolve_exec_target + exec_target_from_env; require→resolved=false signal).
- AC-3 generic algorithm surface over T (reduce/scan/transform/sort/count/filter/find +
  min/max_element/transform_reduce/unique/lower_bound/binary_search/exclusive_scan) —
  **DONE** (compute_ops.spl + compute_algo_ext.spl; 8/16 specs).
- AC-4 container types Span/FixedArray/InplaceVector pure-Simple — **DONE** (containers.spl; 8/8).
- AC-5 cuda/metal/vulkan dispatch wired, honest payload-gated offload, require fail-closed —
  **DONE for routing+gating** (backend_dispatch.spl; 9/9). **Per-backend kernel EMISSION now
  DONE** (gpu_compute_algorithm_kernels.spl; 8/8) — real CUDA/HIP/OpenCL/Metal/WebGPU source
  for transform-scale + saxpy, verified by backend markers, consistent w/ gpu_portable_compute.
  Remaining: runtime GPU EXECUTION on hardware (compile PTX/SPIR-V/metallib + launch + readback)
  needs a device; CPU reference runs meanwhile (no masquerade).
- AC-6 no gpu-named fn silently on CPU (ComputeStats.ran_on_cpu honest) — **DONE**.
- AC-7 built via parallel agent teams; co-goal bugs tracked — **DONE** (3 agents; bug filed).

## Verified
- 52/52 compute specs green (exec_target 11, compute_ops 8, compute_algo_ext 16,
  backend_dispatch 9, containers 8). Run via seed driver.
- Committed: exec_target (f6b8acf-lineage), compute_ops, then containers+restored specs+unique
  fix (d2279d3). Survived a concurrent-session reconcile that stripped specs twice.

## Co-goal bugs found
- B-new1 (REAL, filed): generic `!=`/2-arg-`==` on `[T]` mis-evaluates in interpreter →
  `doc/08_tracking/bug/interp_generic_eq_callback_2026-06-16.md`. Worked around via `less`.
- B-claim2 (REJECTED): "expect(bool).to_be() non-discriminating" — empirically FALSE
  (probe: false.to_be(true) fails, true/false.to_be(matching) pass). Not filed.

## Open / next
- Real GPU-kernel emission per backend (cuda/metal/vulkan) via gpu_portable_compute/@gpu_kernel.
- `std.compute` __init__ namespace export wiring (currently import via full tier path).
- Atomics/Bitset/Complex container parity (B4) — deferred.

## Phase
dev-done → impl landed (foundation + surface + dispatch); GPU-kernel execution open.

## Log
- 2026-06-16: two-level ExecTarget refactor; std.compute surface + containers + dispatch via
  3 parallel agent teams; 52/52 green; generic-eq interp bug found+filed+worked-around.
