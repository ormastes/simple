# Draft NFR — Unified Compute Stdlib: Parity, Verification & Performance

**Status:** DRAFT (Research Step 1) · **Date:** 2026-06-16
**Source:** `doc/01_research/lib/gpu_containers_unified/gpu_containers_algorithms_stdlib_cuda_parity_2026-06-16.md`

## NFR-1 — Cross-backend correctness (differential testing)
Every non-CUDA backend (pure-Simple, Vulkan, Metal) MUST match the CUDA oracle:
- Integer / sort / selection results: **bit-exact**.
- Float reductions/scans: within a **declared tolerance** (summation order differs) — the
  tolerance contract (ULP or relative epsilon) is specified per algorithm, not assumed
  bit-exact.

## NFR-2 — Fail-closed switching
A correctness mismatch, or a missing backend in strict mode, MUST exit non-zero
(reuse the in-repo `rt_exit 70` dual-backend fail-closed pattern) — never silent CPU
degradation behind a `gpu_`/`Cuda` label.

## NFR-3 — Performance (no silent perf cliffs)
- A backend slower than the CPU reference for a target input size is a **perf bug** to file,
  not an acceptable fallback.
- GPU batch performance target tracks the existing model (`host_gpu_lane.md`):
  ≈½ CPU baseline with a 1 ms floor where strict backend evidence exists.
- Naming MUST NOT imply acceleration that does not happen (current `gpu_*` CPU stubs
  violate this — see research §5 B3).

## NFR-4 — No backend fork (architecture)
Algorithms compile through the existing `gpu_portable_compute` MIR path and `@gpu_kernel`;
no new per-backend source tree. New surface lands in the `nogc_async_mut` default tier.

## NFR-5 — Co-goal: bug/enhancement provenance
Each bug/perf-bug found (research §5: B1 iterator protocol, B3 CPU-masquerading gpu_*,
B4 atomics, B5 f64 reliability, B6 array.get corruption, B7 four-resolver debt) MUST get a
tracked bug/feature doc; fixes land with the feature, not deferred indefinitely.
