# U64 Range For-Loop Checksum Mismatch - 2026-05-14

## Status

Resolved for checksum correctness. Performance parity remains open.

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

Original observed checksum mismatch before the compiler fix:

- C/Rust `list_traverse`: `3865411584000`
- Simple `list_traverse` after the `for 0..length` rewrite: `483124838400`
- Simple `set_contains` after the analogous range rewrite: `0`

The compiler now preserves unsigned counter typing for `for 0..u64_bound`
lowering, and the same benchmark probe preserves checksum parity after
rebuilding `src/compiler_rust/target/debug/simple`.

Resolved evidence:

- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler for_range_preserves_u64_counter_type -- --nocapture`
- rebuilt driver with `cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple`
- reran the collection benchmark probe with `for 0..length`; all four
  benchmark checksums matched C/Rust

The probe was still reverted. Keep the collection benchmark on the faster
verified `while` form until range-for optimization performance catches up.

## Impact

The existing SIMD/reduction optimizer only analyzes canonical range `for`
loops, but the current collection benchmark still should not be converted to
that shape because it regressed speed sharply even after checksum correctness
was fixed. Closing the list traversal and scalar membership gaps should either:

- speed up unsigned range-loop lowering/codegen first, or
- add equivalent optimizer support for the existing `while unsigned_index <
  cached_len` shape.
