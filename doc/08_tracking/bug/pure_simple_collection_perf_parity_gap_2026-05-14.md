# Pure Simple collection benchmark parity gap

Date: 2026-05-14

## Summary

Pure Simple collection benchmark performance still does not match the C and
Rust references for traversal and set lookup. `list_push` is currently faster
than Rust, but `list_traverse`, `set_contains`, and source-closure text
`HashSet.contains` remain below parity.

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

Updated source-closure text `HashSet.contains` evidence:

```sh
timeout 80s ./src/compiler_rust/target/debug/simple native-build --clean --runtime-bundle core-c-bootstrap --source src/lib --entry test/perf/collections/collection_simple.spl --entry-closure --backend cranelift --opt-level aggressive -o build/perf/collections/collection_simple_clean && build/perf/collections/collection_simple_clean
```

Observed result after erasing standalone docstring statements and routing the
pure Simple `HashMap` text path through stored hashes plus core-C
`rt_string_eq`: `hashset_contains` measured `17,328` ops/ms with checksum
`13724364800` and no generated-stub warning. This is much faster than the prior
source-closure `190`-`194` ops/ms range, but it still misses C/Rust parity.

The full one-sample clean source-closure harness run also passed checksum
parity, but still emitted speed warnings:

```text
list_traverse    0.28x C  0.16x Rust
list_push        0.65x C  1.28x Rust
set_contains     0.52x C  0.26x Rust
hashset_contains 0.26x C  0.43x Rust
```

After direct `rt_string_eq` branching and power-of-two bucket masking, a later
full clean source-closure harness run still passed checksum parity and measured:

```text
list_traverse    0.21x C  0.20x Rust
list_push        0.43x C  0.84x Rust
set_contains     0.51x C  0.26x Rust
hashset_contains 0.37x C  0.63x Rust
```

Inlining the map probe into `HashSet.contains` then measured:

```text
list_traverse    0.45x C  0.18x Rust
list_push        0.64x C  0.85x Rust
set_contains     0.36x C  0.18x Rust
hashset_contains 0.39x C  0.65x Rust
```

Generic array indexing was then narrowed from `rt_index_get` to `rt_array_get`
when HIR proves the receiver is an array, with a Cranelift inline path for
native builds. Pure `HashMap` and `HashSet` bucket-index helpers now return
`u64`, removing signed negative-index normalization from bucket probes. The
full clean source-closure harness with native CPU kept checksum parity and
measured:

```text
list_traverse    0.52x C  0.19x Rust
list_push        0.89x C  1.11x Rust
set_contains     0.45x C  0.24x Rust
hashset_contains 0.44x C  0.72x Rust
```

The harness now applies `SIMPLE_NATIVE_CPU=native` to Simple source-closure
native builds so the CPU target matches the C/Rust reference settings. A clean
one-sample run with that setting still missed speed floors:

```text
list_traverse    0.26x C  0.25x Rust
list_push        0.44x C  0.90x Rust
set_contains     0.34x C  0.18x Rust
hashset_contains 0.34x C  0.64x Rust
```

The pure Simple `HashSet` was then split from the value-carrying `HashMap`
wrapper into standalone `SetEntry` buckets, and `HashMap.Entry` was renamed to
`HashMapEntry` to avoid facade import collisions. A direct clean source-closure
native run linked a 39 KB binary and measured text `hashset_contains` at
`25,312` ops/ms with checksum parity. The full clean source-closure harness
with native CPU still reported remaining gaps:

```text
list_traverse    0.20x C  0.12x Rust
list_push        0.43x C  2.66x Rust
set_contains     0.52x C  0.27x Rust
hashset_contains 0.39x C  0.65x Rust
```

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
- Native integer comparison lowering now uses unsigned Cranelift compare
  conditions when either operand carries an unsigned integer type. A high-bit
  `u64` JIT regression test passes, and no-strip `bench_list_traverse`
  disassembly changed the loop branches from signed `jl` to unsigned `jb`.
  The 3-sample benchmark still remained below parity:
  `list_traverse` 0.28x vs C / 0.18x vs Rust, `list_push` 0.63x vs C / 1.34x
  vs Rust, and `set_contains` 0.38x vs C / 0.18x vs Rust.
- A flat source-closure text hash path now avoids per-call docstring string
  allocation, stores hash values in `HashMap.Entry`, reuses stored hashes during
  resize, and uses `rt_hash_text`/`rt_string_eq` for text probe checks. This
  closed the accidental receiver-hash mismatch in the prior helper method path,
  but did not close native parity for text `HashSet.contains`.
- Replacing `rt_string_eq(...) != 0` with direct truth branches removed the
  post-compare `rt_native_neq` call in the text probe loop. Adding a
  power-of-two bucket mask removed the signed divide for capacities such as the
  benchmark's 2048 buckets. These changes improved text `HashSet.contains`, but
  C parity is still not closed.
- Moving the text probe into `HashSet.contains` removed the wrapper call to
  `HashMap.contains_key`, but the remaining bucket/entry indexing and string
  equality calls still leave the text set below C.
- Splitting `HashSet` into standalone pure Simple buckets removed the unused
  map value storage and preserved clean facade behavior, but the text lookup
  path is still below C and the broader collection benchmark still depends on
  backend loop-shape improvements.
- Direct `rt_array_get` lowering plus native inlining removes generic
  collection dispatch from known-array indexing, and unsigned bucket indices
  remove signed normalization from text-set probes. These changes improve the
  benchmark but do not close scalar set lookup or Rust traversal parity.

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
For text `HashSet.contains`, inspect the remaining source-closure probe loop
for generic array indexing and method-call overhead before retrying another data
structure rewrite.

## 2026-05-14 Update

The pure runtime and interpreter `rt_hash_text` paths now match the C reference
byte hash (`5381`, then `hash * 33 + byte`) instead of Rust `DefaultHasher`.
Focused hash tests, driver build, and both clean collection facade specs pass.
The clean source-closure benchmark still fails the parity floor: list traversal
`0.26x` C / `0.12x` Rust, list push `0.43x` C / `2.64x` Rust, scalar set
membership `0.34x` C / `0.17x` Rust, and text `HashSet.contains` `0.41x` C /
`0.69x` Rust, with checksum parity preserved. The remaining work is still a
native loop/backend optimization problem, not just collection-library behavior.

The pure Simple push loop now appends four preallocated values per inner-loop
step. A clean source-closure benchmark preserved checksum parity and measured
list push at `1.32x` C / `2.53x` Rust. This does not close the bug: list
traversal remains `0.32x` C / `0.29x` Rust, scalar set membership remains
`0.26x` Rust, and text `HashSet.contains` remains `0.42x` C in the same run.
