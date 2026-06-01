<!-- codex-research -->
# NFR Options: Harden TUI/GUI Layout Comparison

## Option A: Correctness Gate

Description: Require deterministic comparison results, no placeholder SPipe assertions, capture failures reported separately from mismatches, and generated manuals for changed system specs.

Pros: High confidence in comparison correctness; feasible on current host.

Cons: Does not set aggressive performance targets.

Effort: S/M, about 3-8 files.

## Option B: Balanced Size/Perf Gate

Description: Option A plus warm comparison startup under 2 seconds for focused fixtures, no default binary size regression above 5% for changed CLI/tool targets, and max RSS reported for representative comparison runs.

Pros: Practical evidence without requiring every GPU backend locally; catches size/startup regressions.

Cons: Needs stable measurement harness and baseline capture.

Effort: M/L, about 6-14 files.

## Option C: Backend-Qualified Acceleration Gate

Description: Option B plus per-backend Metal, Vulkan, CUDA, and SIMD CPU availability probes, correctness comparison against scalar/software baseline, p50/p95 render+readback timing, and explicit unavailable/blocked reports by backend.

Pros: Best fit for requested Metal/Vulkan/CUDA/SIMD optimization; prevents unsupported backend claims.

Cons: Full PASS depends on hardware/runtime availability or tracked follow-up bugs for unavailable backends.

Effort: L/XL, about 12-28 files.

## Option D: Strict Release Gate

Description: Option C plus release-blocking performance budgets for all supported backends on target hardware, with no unavailable lanes allowed.

Pros: Strongest production gate.

Cons: Not feasible without guaranteed Metal, Vulkan, CUDA, and SIMD-capable target machines in CI or lab access.

Effort: XL, 20+ files and platform infrastructure.
