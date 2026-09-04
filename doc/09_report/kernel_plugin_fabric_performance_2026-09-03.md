# Kernel Plugin Fabric Performance and Capacity Evidence

**Date:** 2026-09-03  
**Status:** Reproducible native evidence gate

## Scope

The gate measures a representative 16 KiB batch through static-direct, cached
static-table, and admitted native-provider operation paths. It separately
measures cold `dlopen`/symbol/descriptor admission, generation-local indexed
pin/cancel work at 64 and 65,536 slots, and fixed queue storage.

## Reproduction

```text
scripts/check/kernel-plugin-fabric/benchmark-performance-capacity.shs
scripts/check/kernel-plugin-fabric/benchmark-performance-capacity-mutation.shs
```

Set `KPF_BENCHMARK_OUTPUT` to retain the complete machine-readable receipt. The
receipt records UTC time, architecture, OS, compiler identity, sample count,
batch size, cold p50/p95, warm medians, paired median signed deltas, overhead
ratios, scaling ratio, and fixed memory bytes.

## Admission Gates

- Static table overhead is at most 1% over static direct for coarse batches.
- Cached native table overhead is at most 5% over static direct.
- Increasing the indexed slot table from 64 to 65,536 entries may increase
  pin/cancel time by at most 2.5x, demonstrating size-independent indexing.
- A 1,024-entry modeled request queue occupies exactly 16,384 bytes and never
  grows during the run.
- Mutation mode executes an actually slower static implementation and must fail
  the normal 1% gate; it also forces the indexed-scaling gate to fail closed.

Warm paths rotate execution order across 21 samples. Overhead is computed from
the median paired signed, saturating delta relative to the direct-path median.
This prevents faster samples from wrapping through unsigned subtraction and
reduces sensitivity to drift between independently timed paths.

These figures measure KPF framework dispatch and capacity behavior, not provider
semantic work or worker IPC. Absolute timings are evidence, not portable limits;
the ratio and fixed-capacity predicates are the release gates.

## Recorded Run

The exact current values below are refreshed by the focused gate run described
in the final section.

| Measure | Result |
|---|---:|
| Cold admission p50 / p95 | 264,000 ns / 471,000 ns |
| Static direct p50 | 53,236,000 ns |
| Static table p50 | 52,847,000 ns |
| Cached native table p50 | 52,049,000 ns |
| Static paired delta p50 | -372,000 ns |
| Native paired delta p50 | -654,000 ns |
| Static overhead | -6,987 ppm (-0.6987%) |
| Native overhead | -12,284 ppm (-1.2284%) |
| 64-slot / 65,536-slot indexed work | 6,007,000 ns / 7,163,000 ns |
| Slot scaling ratio | 1.192442x |
| Fixed 1,024-entry queue storage | 16,384 bytes |

Both the normal admission gate and its real-slowdown/complexity mutation-red
gate passed. Negative overhead values mean the measured variant was faster and
remain signed rather than wrapping to a huge unsigned value. The authoritative
receipt is `build/review/kpf-performance-capacity-20260903.env`.
