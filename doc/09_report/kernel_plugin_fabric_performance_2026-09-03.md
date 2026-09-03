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
batch size, cold p50/p95, warm medians, overhead ratios, scaling ratio, and
fixed memory bytes.

## Admission Gates

- Static table overhead is at most 1% over static direct for coarse batches.
- Cached native table overhead is at most 5% over static direct.
- Increasing the indexed slot table from 64 to 65,536 entries may increase
  pin/cancel time by at most 2.5x, demonstrating size-independent indexing.
- A 1,024-entry modeled request queue occupies exactly 16,384 bytes and never
  grows during the run.
- Mutation mode forces impossible thresholds and must fail closed.

These figures measure KPF framework dispatch and capacity behavior, not provider
semantic work or worker IPC. Absolute timings are evidence, not portable limits;
the ratio and fixed-capacity predicates are the release gates.

## Recorded Run

The 2026-09-03 run used Apple clang 17.0.0 on arm64 Darwin 25.5.0 with 21
samples, 2,048 operations per sample, and 16,384-byte batches.

| Measure | Result |
|---|---:|
| Cold admission p50 / p95 | 230,000 ns / 333,000 ns |
| Static direct p50 | 74,584,000 ns |
| Static table p50 | 74,585,000 ns |
| Cached native table p50 | 74,615,000 ns |
| Static overhead | 13 ppm (0.0013%) |
| Native overhead | 415 ppm (0.0415%) |
| 64-slot / 65,536-slot indexed work | 6,248,000 ns / 8,949,000 ns |
| Slot scaling ratio | 1.432298x |
| Fixed 1,024-entry queue storage | 16,384 bytes |

Both the normal admission gate and its threshold/complexity mutation-red gate
passed. The authoritative reproducible values are emitted by the receipt rather
than inferred from this narrative snapshot.
