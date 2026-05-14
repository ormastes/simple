# U64 Range For-Loop Checksum Mismatch - 2026-05-14

## Status

Open.

## Context

While investigating pure Simple collection parity, converting the verified
`while` loops in `test/perf/collections/collection_simple.spl` to canonical
range `for` loops changed benchmark results instead of preserving behavior.

Probe shape:

```spl
for i in 0..length:
    checksum = checksum + (data[i] ^ iter)
```

where `length` is a cached `u64` from `data.len().to_u64()`.

## Evidence

Command:

```bash
timeout 150s env SIMPLE_COLLECTION_BENCH_SOURCE_CLOSURE=1 SIMPLE_COLLECTION_BENCH_CLEAN=1 SIMPLE_COLLECTION_BENCH_CPU=native test/perf/collections/run_collection_benchmarks.shs
```

Observed checksum mismatch:

- C/Rust `list_traverse`: `3865411584000`
- Simple `list_traverse` after the `for 0..length` rewrite: `483124838400`
- Simple `set_contains` after the analogous range rewrite: `0`

The probe was reverted. Keep the collection benchmark on the verified `while`
form until range lowering over unsigned bounds is fixed and covered by a
regression test.

## Impact

The existing SIMD/reduction optimizer only analyzes canonical range `for`
loops, but the current collection benchmark cannot be safely converted to that
shape. Closing the list traversal and scalar membership gaps should either:

- fix unsigned range-loop lowering first, or
- add equivalent optimizer support for the existing `while unsigned_index <
  cached_len` shape.
