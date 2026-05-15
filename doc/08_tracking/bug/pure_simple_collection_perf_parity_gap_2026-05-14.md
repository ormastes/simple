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

## 2026-05-14 Late Update

Two pure-Simple runtime commits were pushed as ancestors of remote `main`:

- `613c7e961605` — `Reduce address math in pure Simple numeric kernels`
- `6a483d70be04` — `Close pure Simple contains parity gaps`

The first commit changes the u64 xor-sum and contains kernels to walk a moving
data pointer instead of recomputing `idx * 8` for every load. The second commit
uses byte occupancy flags for the pure Simple `HashSet` probe table and
strength-reduces the reduction return path.

Latest 5-sample source-closure benchmark, with `simple-core`, native CPU, clean
runtime archive rebuild, and checksum parity:

```text
list_traverse     0.71x C / 0.43x Rust
list_push         1.31x C / 2.54x Rust
set_contains      1.02x C / 0.51x Rust
hashset_contains  0.52x C / 0.88x Rust
```

Only `list_traverse` remains below the 0.50x Rust floor in that pushed baseline.
Disassembly of `rt_numeric_xor_sum_u64` shows direct scalar unrolled loads over
the raw data pointer with no per-element runtime helper calls. A
two-accumulator variant, text-hash cursor variant, and cached HashSet mask
variant all regressed benchmark results and were reverted.

## 2026-05-14 Vector Reduction Update

A Cranelift callsite inline path for `rt_numeric_xor_sum_u64` now emits a
two-lane vector accumulator over raw u64 array data, with scalar tail handling
and the same array validity checks as the pure Simple runtime helper. Focused
u64 xor-sum lowering tests and the compiler driver build pass.

Clean five-sample source-closure benchmark evidence with `simple-core`,
`SIMPLE_NATIVE_CPU=native`, clean runtime archive rebuild, and checksum parity:

```text
list_traverse     1.35x C / 0.71x Rust
list_push         1.34x C / 2.58x Rust
set_contains      0.79x C / 0.41x Rust
hashset_contains  0.48x C / 0.82x Rust
```

This closes the old `list_traverse` floor, but the overall parity issue is not
closed. `set_contains` is still below the 0.50x Rust floor, and
`hashset_contains` was just below the 0.50x C floor in this noisy run.
Unchecked contains lowering, callsite contains inlining, vector contains
probing, and broader loop-function inlining were tried locally and reverted
because they either did not close the set floor or regressed it. The remaining
work is now a typed contiguous contains/probe optimization problem rather than
a typed reduction problem.

## 2026-05-14 Lookup Follow-up

After reverting the unproven alias-lowering branch, a fresh clean-worktree
warning-mode benchmark on pushed `main` preserved checksum parity and measured:

```text
list_traverse     1.03x C / 0.63x Rust
list_push         1.28x C / 2.51x Rust
set_contains      0.81x C / 0.33x Rust
hashset_contains  0.50x C / 0.83x Rust
```

The durable miss is now scalar `set_contains` against Rust. Disassembly of the
native benchmark shows `bench_set_contains` already calls
`rt_numeric_contains_u64` directly from the hot loop; the local Simple
`set_contains` wrapper is reduced to a small runtime-kernel call. The remaining
cost is therefore inside the generated/runtime contains scan shape, not a missed
local helper call.

Additional local experiments were rejected:

- Alias-proof lowering plus non-tail MIR inlining still left `set_contains`
  around `0.31x` Rust in the combined benchmark.
- Replacing the text HashSet contains mask expression with `hash.to_u64() &
  mask` did not lift the borderline C floor.
- A Cranelift callsite inline for `rt_numeric_contains_u64` using `I64X2`
  compare masks, little-endian `I128` bitcasts, and `bmask(I64, ...)` compiled
  successfully but failed the benchmark gate. A one-sample warning-mode run
  preserved checksum parity, but measured `set_contains` at only `0.59x` C /
  `0.24x` Rust and severely regressed text `hashset_contains`. The experiment
  was reverted.
- Cranelift 0.116 exposes no simple frontend `any lane true` / vector bitmask
  operation for integer compare masks, so the prior lane-extract vector contains
  experiment remains the wrong path.

Next useful work should focus on the `rt_numeric_contains_u64` native code
shape itself: a target-aware x64 lowering, a Cranelift-compatible compare-mask
strategy that avoids lane extraction, or a scalar layout that reduces branch
pressure while preserving early exit.

## 2026-05-14 Single-Exit Contains Follow-up

The pure Simple `rt_numeric_contains_u64` helper now preserves early exit but
routes successful chunk and tail probes through one final return path instead
of duplicating a full return at every compared lane. This trims the generated
contains shape without changing checksum behavior.

Before benchmarking the explicit `simple-core` lane, rebuild the pure runtime
archive:

```sh
SIMPLE_NATIVE_CPU=native src/compiler_rust/target/debug/simple native-build --source src/runtime/simple_core --no-mangle --emit-archive --output build/simple-core/libsimple_runtime.a --clean
```

Without that archive rebuild, the collection harness can select a stale
simple-core archive and generate a stub for `rt_numeric_contains_u64`, which
makes the set benchmark invalid. After rebuilding, `nm` showed both
`rt_numeric_contains_u64` and `rt_numeric_xor_sum_u64` exported.

Clean three-sample source-closure benchmark evidence with `simple-core`,
`SIMPLE_NATIVE_CPU=native`, rebuilt runtime archive, and checksum parity:

```text
list_traverse     1.29x C / 1.05x Rust
list_push         1.28x C / 4.59x Rust
set_contains      0.82x C / 0.34x Rust
hashset_contains  0.57x C / 0.92x Rust
```

The change improves the scalar contains shape only modestly; `set_contains`
still misses Rust parity and remains the open blocker. A variant that loaded
all eight chunk values first and used one compound `or` condition regressed
`set_contains` to `0.17x` Rust in a one-sample clean run and was reverted.
Rust's reference binary uses AVX `vpcmpeqq` plus a vector test for this scan.
A direct Cranelift `I64X4` compare plus `bmask(I64, mask)` experiment was also
rejected: Cranelift 0.116 verifies `bmask` only for scalar integer inputs, so
the benchmark compile failed before producing a valid binary.

## 2026-05-15 Contains Vector Test Update

The native callsite inline for `rt_numeric_contains_u64` now uses four
`I64X2` vector compares, ORs the compare masks, and applies Cranelift
`vany_true` once per eight-element chunk. On x64 this lowers to
`vpcmpeqq`/`vpor`/`vptest`, avoiding the failed `bmask` path and the earlier
per-lane extraction shape.

Clean three-sample source-closure benchmark evidence with `simple-core`,
`SIMPLE_NATIVE_CPU=native`, rebuilt runtime archive, and checksum parity:

```text
list_traverse     0.77x C / 0.48x Rust
list_push         1.29x C / 2.63x Rust
set_contains      1.50x C / 0.60x Rust
hashset_contains  0.48x C / 0.80x Rust
```

Disassembly of `set_contains` confirms the hot chunk path uses four
`vpcmpeqq` instructions, three `vpor` instructions, and one `vptest` per
eight-element chunk. This closes the scalar `set_contains` Rust floor in the
sample above. The remaining parity risk is now the noisy `list_traverse` Rust
floor and text `hashset_contains` C floor.

Follow-up experiments rejected:

- Splitting the `rt_numeric_xor_sum_u64` callsite inline into two `I64X2`
  accumulators passed the existing xor-sum and contains lowering tests, but a
  clean five-sample benchmark still left `list_traverse` at `0.71x` Rust and
  pushed `hashset_contains` below the C warning floor (`0.49x` C). The change
  was reverted.
- Moving `HashSet.contains` to a pure Simple runtime helper
  `rt_hashset_text_contains` avoided generic library indexing at the callsite
  but regressed the text membership benchmark to `0.27x` C / `0.43x` Rust in a
  clean five-sample source-closure run. The helper was reverted.
- Adding a byte-loop short-string fast path to pure Simple `rt_string_eq`
  avoided libc `memcmp` for the benchmark's small keys, but still measured
  `hashset_contains` at `0.49x` C / `0.81x` Rust in a clean five-sample run.
  The fast path was reverted.
