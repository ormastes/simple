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
- Splitting the vector `rt_numeric_contains_u64` callsite inline into two
  four-element tests preserved the targeted contains lowering test, but a clean
  five-sample benchmark still left `set_contains` at only `0.60x` Rust while
  warning on `list_traverse` (`0.45x` Rust) and `hashset_contains` (`0.48x`
  C). The split-chunk shape was reverted.

Current clean pushed-state baseline after reverting those experiments and
rebuilding `simple-core`:

```text
list_traverse     1.23x C / 0.71x Rust
list_push         1.23x C / 2.74x Rust
set_contains      1.41x C / 0.64x Rust
hashset_contains  0.48x C / 0.82x Rust
```

Checksum parity passed. `hashset_contains` remains below the current C warning
floor, so the parity objective is still open.

Additional `HashSet.contains` raw-probe experiments rejected:

- Raw-loading both `slot_used` and `slot_keys` through `rt_array_data_ptr` and
  `spl_load_*` failed checksum parity; `hashset_contains` returned zero hits.
- Raw-loading only `slot_used` preserved checksum parity but still measured
  `hashset_contains` at `0.49x` C in a clean three-sample run.
- Raw-loading `slot_keys` and comparing with `rt_string_eq` preserved checksum
  parity but regressed `hashset_contains` to `0.44x` C / `0.73x` Rust.
- Raw-loading `slot_keys` and comparing with `rt_native_eq` preserved checksum
  parity but regressed further to `0.42x` C / `0.71x` Rust.
- Replacing `keys[slot] == value` with explicit
  `rt_native_eq(keys[slot], value) != 0` preserved checksum parity but
  regressed `hashset_contains` to `0.40x` C / `0.66x` Rust. The source-level
  equality rewrite was reverted.

## 2026-05-15 HashSet Probe Density Update

Pure Simple `HashSet.with_capacity` now normalizes twice the requested capacity.
The public contract remains "at least this capacity", while the lower load
density reduces successful text-probe chains without adding raw pointer
shortcuts.

Clean five-sample source-closure benchmark evidence with rebuilt `simple-core`,
`SIMPLE_NATIVE_CPU=native`, and checksum parity:

```text
list_traverse     1.08x C / 0.90x Rust
list_push         1.28x C / 2.63x Rust
set_contains      1.28x C / 0.53x Rust
hashset_contains  0.58x C / 0.98x Rust
```

Focused tests:

- `simple test test/unit/lib/nogc_sync_mut/hashset_probe_spec.spl --mode=interpreter`
- `simple test test/unit/lib/nogc_async_mut/src/collections/src_collections_facade_spec.spl --mode=interpreter`
- `simple test test/unit/lib/gc_async_mut/src/collections/src_collections_facade_spec.spl --mode=interpreter`

## 2026-05-15 Contains Scan Second-Chunk Update

The native codegen callsite inline for `rt_numeric_contains_u64` now tests two
eight-element `I64X2` vector chunks before looping when a second chunk is
available. The first chunk still branches to the scalar tail for short arrays,
so the transform keeps the previous small-tail behavior while reducing loop
branch overhead for the benchmark's 1024-element scan.

Focused compiler validation:

- `cargo build -p simple-driver --bin simple`
- `cargo test -p simple-compiler simd_auto_lowers_canonical_while_u64_contains_to_runtime_kernel -- --nocapture`

Clean five-sample source-closure benchmark evidence with rebuilt `simple-core`,
`SIMPLE_NATIVE_CPU=native`, and checksum parity:

```text
list_traverse     1.33x C / 0.85x Rust
list_push         1.29x C / 4.46x Rust
set_contains      1.66x C / 0.66x Rust
hashset_contains  0.61x C / 0.96x Rust
```

This improves the scalar set scan and clears the current benchmark warning
floor, but strict parity is still open because `list_traverse` remains below
Rust and `hashset_contains` remains below C.

## 2026-05-15 Xor Scan And Trusted Byte Index Update

The native codegen callsite inline for `rt_numeric_xor_sum_u64` now mirrors the
contains lowering by accumulating a second eight-element `I64X2` chunk before
looping when the second chunk is available. Trusted `rt_typed_bytes_u8_at`
lowering now also loads the packed byte directly after bounds validation; this
removes the per-probe packed-layout branch from pure Simple `HashSet.slot_used`
lookups.

Focused compiler validation:

- `cargo build -p simple-driver --bin simple`
- `cargo test -p simple-compiler typed_bytes_u8 -- --nocapture`
- `cargo test -p simple-compiler u64_ -- --nocapture`

Clean five-sample source-closure benchmark evidence with rebuilt `simple-core`,
rebuilt driver, `SIMPLE_NATIVE_CPU=native`, and checksum parity:

```text
list_traverse     1.27x C / 0.67x Rust
list_push         0.90x C / 1.69x Rust
set_contains      1.81x C / 0.72x Rust
hashset_contains  0.61x C / 0.99x Rust
```

This improves `set_contains` again and removes byte occupancy dispatch from the
hashset probe, but strict parity remains open. `hashset_contains` is still below
the C fixed-table reference, and the median-selected `list_traverse` Rust ratio
remains noisy across five-sample runs.

Rejected follow-up:

- Seeding parameter VRegs into the native codegen type map and routing
  string-typed equality through `rt_string_eq` passed focused `vreg_types` and
  u64 equality tests, but failed the clean source-closure collection build:
  `missing runtime fn 'rt_string_eq' in HashSet.insert`. The experiment was
  reverted rather than adding another runtime-map dependency to the pure Simple
  source-closure path.
- Declaring `rt_string_eq(left: text, right: text)` in the pure Simple
  `HashSet` source and using it for insert/contains key comparisons preserved
  the focused nogc_sync and nogc_async collection tests, but failed the
  gc_async collection facade spec with `semantic: type mismatch: cannot convert
  string to int`. The source-level rewrite was reverted.
- Inlining `rt_hash_text` in native codegen removed the runtime hash call and
  passed focused codegen tests, but a rebuilt clean five-sample source-closure
  collection run still measured `hashset_contains` at only `0.59x C / 0.98x
  Rust` and dipped `list_push` to `0.87x C`. The inline hash lowering was
  reverted.

## 2026-05-15 HashSet Sparse Probe Update

Pure Simple `HashSet.with_capacity` now normalizes `capacity * 8` for its
standalone open-addressed probe table. The public contract still guarantees at
least the requested capacity, and the extra sparsity reduces collision-chain
work in the hot `contains` path without adding new runtime symbols.

Rejected local variant:

- `capacity * 16` preserved checksum parity but did not improve the
  `hashset_contains` median over `capacity * 8` in a clean three-sample run, so
  it was reverted to avoid extra memory use without measured benefit.
- Reducing the retained probe-table allocation to `capacity * 2` preserved
  checksum parity but measured `hashset_contains` at only `0.60x C / 1.05x
  Rust` in a clean three-sample run. Reducing further to the C-sized
  `capacity` table regressed to `0.50x C / 0.83x Rust` and triggered the
  benchmark warning threshold. Both locality variants were reverted; the
  retained `capacity * 8` table still provides the best observed C ratio.

Focused validation:

- `simple test test/unit/lib/nogc_sync_mut/hashset_probe_spec.spl --mode=interpreter`
- `simple test test/unit/lib/nogc_async_mut/src/collections/src_collections_facade_spec.spl --mode=interpreter --no-cache`
- `simple test test/unit/lib/gc_async_mut/src/collections/src_collections_facade_spec.spl --mode=interpreter --no-cache`

Clean five-sample source-closure benchmark evidence with rebuilt `simple-core`,
`SIMPLE_NATIVE_CPU=native`, and checksum parity:

```text
list_traverse     1.04x C / 0.84x Rust
list_push         1.31x C / 2.56x Rust
set_contains      1.86x C / 0.74x Rust
hashset_contains  0.65x C / 1.08x Rust
```

This lifts `hashset_contains` over the Rust reference in this run, but strict
parity remains open because it is still below the C fixed-table reference and
`list_traverse` / `set_contains` remain below Rust in the median-selected run.

Rejected follow-up:

- A type-directed native codegen inline for `text == text` seeded parameter and
  string-literal VRegs, emitted byte equality directly, and passed focused
  compiler tests proving no `rt_native_eq` / `rt_string_eq` relocation for a
  direct string equality object. A rebuilt three-sample source-closure
  collection run preserved checksum parity but regressed `hashset_contains` to
  `0.55x C / 0.99x Rust`, so the codegen change was reverted.
- Expanding the `rt_numeric_xor_sum_u64` callsite lowering from two
  eight-element chunks per loop to four compiled and passed focused `u64_`
  compiler tests, but a rebuilt three-sample source-closure collection run
  preserved checksum parity while regressing `list_traverse` to `0.98x C /
  0.51x Rust`. The codegen change was reverted.
- Simplifying pure Simple `rt_native_eq` comparisons from `< or >` tests to
  `!=` for string kind, `memcmp`, and raw value equality preserved checksum
  parity but did not improve `hashset_contains` (`0.62x C / 1.02x Rust`) and
  pushed `list_push` below C (`0.90x`) in a clean three-sample run. The runtime
  source change was reverted.
- Allowing the existing MIR small-function inliner to inline callees with
  back-edges broke the explicit `does_not_inline_loop_callees_without_licm`
  test and did not remove the hot `set_contains` call from the generated
  collection benchmark binary. The benchmark still preserved checksum parity,
  but the intended call-boundary optimization did not happen, so the inliner
  change was reverted.
- Raising the MIR inliner limits to 16 blocks / 96 instructions and allowing
  returning loop callees removed the hot `set_contains` call boundary and passed
  updated focused inliner tests, but the clean five-sample source-closure
  benchmark regressed `list_traverse` below C (`0.90x C / 0.73x Rust`) while
  only nudging `set_contains` to `0.76x Rust`. The bounded loop-inliner change
  was reverted.
- Folding non-float `x == x` / `x != x` in native codegen passed a focused
  object relocation test, but it did not remove the `rt_native_eq(length,
  length)` guard from the generated `set_contains` function and regressed the
  retained five-sample `hashset_contains` median to `0.59x C`. The fold was
  reverted.

## 2026-05-15 HIR Length-Alias SIMD Guard Update

HIR SIMD lowering now tracks local aliases created from `array.len().to_u64()`
while rewriting statement blocks. When a canonical `while i < length` loop uses
that local alias and indexes the same array, the lowered numeric runtime kernel
no longer emits the redundant `rt_native_eq(length, length)` bound guard.

Focused validation:

- `rustfmt --check compiler/src/pipeline/lowering.rs compiler/src/pipeline/mod.rs`
- `cargo test -p simple-compiler simd_auto_lowers_canonical_while_u64 -- --nocapture`
- `cargo build -p simple-driver --bin simple`
- `simple check src/compiler` (completed with existing warnings)
- `simple check src/lib` (completed with existing warnings)

Generated-code evidence:

- `objdump` of `collection_simple` shows `set_contains` starts directly with
  array tag/length validation and vector scan setup; the previous
  `rt_native_eq(length, length)` call is gone.
- `nm -u build/perf/collections/collection_simple` still lists only libc/OS
  primitives and weak optional startup hooks; no unresolved Rust runtime symbols.

Clean five-sample source-closure benchmark evidence with rebuilt `simple-core`,
rebuilt driver, `SIMPLE_NATIVE_CPU=native`, and checksum parity:

```text
list_traverse     1.52x C / 1.29x Rust
list_push         1.32x C / 4.50x Rust
set_contains      1.83x C / 0.83x Rust
hashset_contains  0.61x C / 1.04x Rust
```

This removes a real compiler-generated guard and improves the retained
`list_traverse` and `set_contains` Rust ratios, but strict parity remains open:
`set_contains` still trails Rust and `hashset_contains` still trails C.

## 2026-05-15 HashSet Insert Coverage Update

The collection benchmark now includes `hashset_insert` across C, Rust, and pure
Simple with checksum parity. The pure Simple `HashSet` insert path no longer
maintains the unused legacy chained bucket arrays; membership is owned by the
flat probe table and traversal/set algebra by `items`.

Clean five-sample source-closure benchmark after this cleanup:

```text
list_traverse     1.14x C / 0.81x Rust
list_push         1.31x C / 2.57x Rust
set_contains      1.95x C / 0.77x Rust
hashset_contains  0.67x C / 1.04x Rust
hashset_insert    0.01x C / 0.06x Rust
```

`hashset_insert` is now covered and checksum-equivalent, but it exposes a larger
pure Simple construction/insert gap. Removing the dead bucket maintenance
improved the probe insert ratio from about `0.02x Rust` to about `0.06x Rust`;
it is still far from parity.

Rejected broader benchmark probes:

- Adding `hashset_remove` showed checksum mismatch against C/Rust before the
  retained bucket cleanup. The operation needs a dedicated correctness test
  before it becomes benchmark evidence.
- Adding `hashset_intersection` showed checksum mismatch against the reference
  probe and was not retained as parity evidence.
- Adding `hashmap_contains_get` crashed the native benchmark binary during the
  Simple run, so HashMap parity remains an explicit follow-up instead of a
  committed benchmark lane.
