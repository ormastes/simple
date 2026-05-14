# Pure Simple collection benchmark parity gap

Date: 2026-05-14

## Summary

Pure Simple collection benchmark performance still does not match the C and
Rust references for traversal and set lookup. `list_push` is currently faster
than Rust, but `list_traverse` and `set_contains` remain below parity.

## Evidence

Command:

```sh
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_COLLECTION_BENCH_SAMPLES=1 bash test/perf/collections/run_collection_benchmarks.shs
```

Observed ratios:

```text
list_traverse simple_vs_c 0.41x simple_vs_rust 0.25x
list_push     simple_vs_c 0.59x simple_vs_rust 1.20x
set_contains  simple_vs_c 0.38x simple_vs_rust 0.20x
```

Checksum parity passed for all three benchmarks.

## Ruled Out

- The Simple benchmark is not doing a different asymptotic algorithm for
  `set_contains`; the C reference also uses a linear scan over 1024 keys.
- MIR lowering already uses hoisted typed-array raw data reads in the hot
  traversal paths:
  - `bench_list_traverse` uses `rt_array_data_ptr` plus
    `rt_typed_words_u64_raw_data_at`.
  - `set_contains` uses `rt_array_data_ptr` plus
    `rt_typed_words_u64_raw_data_at`.
- Manually inlining the `set_contains` helper into a scratch copy of the
  benchmark did not improve the set benchmark; it was slower in the local run.
- Rewriting the Simple benchmark source to combine a four-wide
  `bench_list_traverse` body with an inline `bench_set_contains` probe loop
  preserved checksum parity but regressed all ratios in a 3-sample local run:
  `list_traverse` 0.21x vs C / 0.14x vs Rust, `list_push` 0.39x vs C / 0.82x
  vs Rust, and `set_contains` 0.15x vs C / 0.08x vs Rust. The source rewrite
  was reverted.
- LLVM backend vectorization is not available in the current compiler build:
  `--backend=llvm` reports that the native LLVM backend is unavailable.
- Rewriting the zero-based inner `while i < length` xor traversal to the
  existing `rt_numeric_xor_sum_u64` runtime kernel is not a viable shortcut for
  the current `core-c` native bundle. A local probe preserved checksum parity
  but regressed `list_traverse` from roughly 1.48M ops/ms to roughly 0.18M
  ops/ms, so the probe was reverted instead of committed.
- No-strip disassembly of the native benchmark confirms the current
  `bench_list_traverse` inner loop is already a direct raw load and xor:
  `xor (%r10,%r11,8), %rax`. The generated loop is scalar and not unrolled;
  this makes the remaining gap a backend loop-shape issue rather than an
  avoidable runtime helper call in the hot load path.
- A native codegen MIR inliner now removes supported small local tail calls.
  No-strip disassembly of `bench_set_contains` confirmed the hot
  `call set_contains` instruction was removed while checksum parity still
  passed. The 3-sample benchmark remained below parity:
  `list_traverse` 0.34x vs C / 0.20x vs Rust, `list_push` 0.59x vs C / 1.33x
  vs Rust, and `set_contains` 0.37x vs C / 0.19x vs Rust.

## Likely Gap

The current native path is Cranelift scalar codegen. The hot loops are direct
raw loads, but they are not vectorized or unrolled like the C/Rust `-O3`
reference builds. Matching C/Rust speed likely needs a real loop transform in
the Simple optimization plug or backend that emits efficient native loop code
over raw typed array data, not a boxed `RuntimeValue` runtime-call
substitution.

## Next Step

Add a focused loop optimization pass for typed contiguous array scans, then
verify with this benchmark. The pass should preserve checksum parity and should
target `list_traverse` and `set_contains` before broader collection rewrites.
