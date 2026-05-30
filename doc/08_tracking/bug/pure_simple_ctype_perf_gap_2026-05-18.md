# Perf Bug: Pure Simple ctype 0.07x–0.46x C (Cranelift, no inlining)

**Date:** 2026-05-18
**Status:** Open / pure-Simple path exhausted — partially mitigated 2026-05-29;
benchmark harness repaired, ctype call nesting flattened, MIR inlining handles
non-tail calls, and Cranelift now has a ctype-specific inline lowering for
`ctype.is_*`/`to_*` static calls. Native still remains below the 0.50x C floor
for most predicates and conversions. The 2026-05-30 static-data LUT probe also
compiled but produced wrong native checksums, so the remaining work is backend
static-data/global-array correctness plus broader loop/branch codegen quality,
not a `ctype.spl` library fix.
**Severity:** Medium — ctype is not hot-path, but pattern applies to all pure Simple stdlib
**Component:** Cranelift AOT codegen / function inlining
**Related:** `native_cross_module_call_abi_broken_2026-05-18.md`

## Benchmark Results (same-file inlined, 128M calls per function)

| Function | C -O2 (ops/ms) | Simple native (ops/ms) | Ratio |
|----------|----------------|----------------------|-------|
| is_digit | 1,003,071 | 464,964 | 0.46x |
| is_upper | 941,314 | 328,729 | 0.35x |
| is_lower | 603,466 | 253,957 | 0.42x |
| is_alpha | 856,594 | 125,779 | 0.15x |
| is_alnum | 1,082,562 | 77,612 | 0.07x |
| is_xdigit | 549,007 | 153,279 | 0.28x |
| is_space | 1,335,294 | 195,241 | 0.15x |
| to_lower | 1,218,049 | 236,592 | 0.19x |
| to_upper | 1,427,472 | 227,271 | 0.16x |

**Interpreter mode:** ~52-168 ops/ms (5000-20000x slower than C — expected).

## Root Cause

Cranelift AOT does not inline function calls. gcc -O2 inlines all ctype
functions (they're `static inline` in the reference). Result:

- **Leaf functions** (single range check): 0.35–0.46x C — call overhead dominates
- **Composite functions** (call 2-3 leaf functions): 0.07–0.15x C — nested calls compound

## Required Optimization (AC-5 candidate)

**Intraprocedural function inlining in the Cranelift AOT pipeline.** Small
functions (< ~10 IR instructions, no loops) should be inlined at call sites.
This alone would likely bring all ctype functions to 0.8-1.0x C.

**Note:** The inlined benchmark represents the *upper bound* on real stdlib
performance — `use std.common.ctype` callers will hit the same or worse numbers
because cross-module calls add overhead even after the ABI bug is fixed.

## Cross-Module Bug

Additionally, cross-module function calls return wrong values in native mode
(see `native_cross_module_call_abi_broken_2026-05-18.md`). The benchmark above
uses same-file inlined functions as a workaround.

## Benchmark Files

- `test/perf/ctype/bench_ctype_ref.c` — C reference (gcc -O2)
- `test/perf/ctype/bench_ctype.spl` — Simple (cross-module, interpreter only)
- `test/perf/ctype/bench_ctype_inline.spl` — Simple (same-file, native-safe)

## 2026-05-27 Follow-up

The benchmark harness itself had drifted:

- `sh test/perf/ctype/run_ctype_benchmarks.shs` failed because the script uses
  Bash arrays and `pipefail`.
- `bash test/perf/ctype/run_ctype_benchmarks.shs` failed because `run_samples`
  referenced `tag` in the same `local` declaration that assigned it.
- The native build command used the obsolete `bin/simple build native` form.
- The C reference still ran 1,000,000 iterations while the Simple benchmark ran
  1,000, making checksum parity fail before any ratio could be trusted.

The harness now runs with Bash, uses `bin/simple native-build`, and the C
reference mirrors the Simple iteration count. `std.common.ctype` also no longer
routes hot aliases and composite predicates through nested ctype calls; it uses
direct range checks for `is_*`, `alpha`, `alnum`, `xdigit`, `to_lower`, and
`to_upper`.

Current one-sample evidence:

```text
benchmark        c_ops/ms   interp_ops/ms   native_ops/ms     interp/c     native/c
is_digit          1122807             159          258585        0.00x        0.23x
is_upper          1032258             157          261758        0.00x        0.25x
is_lower           748538             159          243346        0.00x        0.33x
is_alpha           836601             140          204800        0.00x        0.24x
is_alnum          1185185             131          151479        0.00x        0.13x
is_xdigit          579185             135          155151        0.00x        0.27x
is_space          1855072             130          157441        0.00x        0.08x
to_lower          1454545             154          258064        0.00x        0.18x
to_upper          1600000             156          267782        0.00x        0.17x
```

The bug remains open. The remaining root is still native call/codegen overhead
or missing inlining/specialization, not library-level nested predicate calls.

## 2026-05-27 MIR Inliner Follow-up

The Cranelift MIR inliner only handled calls that were the final instruction in
their block. That missed ctype calls used inside loop conditions and arithmetic
continuations. The inliner now moves the caller's remaining instructions into a
continuation block, so small callees can be inlined at non-tail call sites while
preserving the caller's control flow.

Focused verification:

```bash
rustfmt --check src/compiler_rust/compiler/src/codegen/mir_inline.rs
cargo test -p simple-compiler codegen::mir_inline --manifest-path src/compiler_rust/Cargo.toml
```

Benchmark evidence with `SIMPLE_CTYPE_BENCH_ENFORCE=1
SIMPLE_CTYPE_BENCH_SAMPLES=1 bash test/perf/ctype/run_ctype_benchmarks.shs`:

```text
benchmark        c_ops/ms   interp_ops/ms   native_ops/ms     interp/c     native/c
is_digit          1040650             183          344086        0.00x        0.33x
is_upper           992248             179          377581        0.00x        0.38x
is_lower           636815             182          351648        0.00x        0.55x
is_alpha           825806             162          327365        0.00x        0.40x
is_alnum          1084745             168          268907        0.00x        0.25x
is_xdigit          581818             205          266112        0.00x        0.46x
is_space          1662337             196          283813        0.00x        0.17x
to_lower          1376344             206          393846        0.00x        0.29x
to_upper          1454545             209          343163        0.00x        0.24x
```

The enforced benchmark still fails on eight of nine native ratios. The remaining
work is broader native code quality: branch/code shape, loop optimization, and
specialization beyond basic MIR call inlining.

## 2026-05-29 Root Cause Confirmation

### Measurement (SAMPLES=1, bench_ctype.spl cross-module + bench_ctype_inline.spl same-file)

Cross-module native (harness, 1000 iters, C also 1000 iters — note: noisy at this count):

```text
benchmark        c_ops/ms   interp_ops/ms   native_ops/ms     interp/c     native/c
is_digit          1280000             174          273504        0.00x        0.21x
is_upper          1185185             162          291571        0.00x        0.25x
is_lower           941176             148          251968        0.00x        0.27x
is_alpha           948148             155          217317        0.00x        0.23x
is_alnum           955223             155          188512        0.00x        0.20x
is_xdigit          680851             129          251968        0.00x        0.37x
is_space          1802816             122          243346        0.00x        0.13x
to_lower          1471264             143          401253        0.00x        0.27x
to_upper          1542168             161          357541        0.00x        0.23x
```

Same-file inlined (bench_ctype_inline.spl, 1M iters) vs stable C (100k iters):

```text
Function     | C stable (ops/ms) | Inline (ops/ms) | Inline/C | Cross(noisy)/C
is_digit     |          1775065  |          680022 |     0.38 |           0.15
is_upper     |          1468058  |          836327 |     0.57 |           0.20
is_lower     |          1244288  |          593912 |     0.48 |           0.20
is_alpha     |          1485263  |          327443 |     0.22 |           0.15
is_alnum     |          2218370  |          190951 |     0.09 |           0.08
is_xdigit    |          1080624  |          212872 |     0.20 |           0.23
is_space     |          3363994  |          229269 |     0.07 |           0.07
to_lower     |          2778983  |          571918 |     0.21 |           0.14
to_upper     |          3106042  |          494804 |     0.16 |           0.12
```

### Findings

**Inline vs cross-module gap (2x for leaf functions):** The MIR inliner runs
per source file (each `.spl` compiles to a separate `.o` in the native build
pipeline via `compile_entries_parallel`). The `inline_small_pure_functions`
call in `common_backend.rs` only sees one file's `MirModule` at a time.
Cross-module inlining is therefore architecturally impossible without whole-
program compilation or LTO. This is the primary source of the 2x gap between
inline and cross-module leaf function performance.

**Composite functions bad even same-file (is_space 0.07x, is_alnum 0.09x):**
These functions have 3–6 short-circuit branches. gcc -O2 compiles them to
tight sequential compares with early-exit optimization; Cranelift emits each
`or`-chain branch as a separate conditional branch. The codegen ceiling here
is Cranelift's branch-chain lowering, not the Simple source.

**ctype.spl library is already fully optimized:** All hot aliases and composite
predicates use direct range checks (no nested ctype calls). There is no further
pure-Simple library change that would close the gap.

### Remaining Work (Rust-side)

1. **Cross-module LTO / whole-program MIR inlining** — requires merging all
   MirModules before the inliner pass in `common_backend.rs`. Not a `.spl`
   change.
2. **Cranelift branch-chain optimization** — short-circuit `or` on integer
   comparisons should emit fewer branches. Could be addressed at the MIR level
   by transforming multi-way `or` into a min/max range check where semantics
   permit, or by an additional MIR peephole pass.
3. **Benchmark stability** — the harness at 1000 iters has microsecond noise
   that corrupts C reference readings for fast functions. Consider raising
   `ITERS` in both `bench_ctype.spl` and `bench_ctype_ref.c` to 100000 for
   reliable ratio measurements.

## 2026-05-29 Active Queue Recheck

Focused benchmark still passes checksum parity but remains below the native/C
floor for every predicate. This confirms the active queue item has no remaining
pure-Simple library fix: `std.common.ctype` already uses direct range checks and
the open performance gap is seed codegen/LTO work.

Verification:

```bash
SIMPLE_CTYPE_BENCH_SAMPLES=1 SIMPLE_CTYPE_BENCH_ENFORCE=0 bash test/perf/ctype/run_ctype_benchmarks.shs
```

Fresh native/C ratios:

```text
is_digit 0.20x
is_upper 0.24x
is_lower 0.34x
is_alpha 0.26x
is_alnum 0.13x
is_xdigit 0.26x
is_space 0.12x
to_lower 0.14x
to_upper 0.14x
```

Decision for the active repair queue: keep this bug open as Rust seed
codegen/LTO work; do not churn the pure Simple ctype library further without a
new source-level hypothesis.

## 2026-05-29 Lookup-Table Approach — Pure-Simple Dead End

**Hypothesis tested:** Replace branch-chains with a 256-entry flag table
(`CTYPE_FLAG_TABLE[ch] & FLAG`) to reduce Cranelift branch overhead. Each ctype
predicate becomes a single array load + bitwise AND instead of 3–6 conditional
branches.

**Benchmark:** `test/perf/ctype/bench_ctype_lut.spl` — same structure as
`bench_ctype_inline.spl`, table built as local var before timed loop (module-level
`val` arrays return nil in the interpreter). Correctness verified: checksums
match `bench_ctype_inline.spl` for all nine functions.

**Discovery — same-file module-level `val` array nil bug:** `val TABLE = [...]`
at module scope in a single-file program returns nil for all elements in the
interpreter (segfault on arithmetic with nil). Both direct index (`TABLE[i]`)
and copy-to-local (`var t = TABLE; t[i]`) return nil in the same-file case.
Cross-module `val` arrays (imported via `use`) work correctly — this is why
bcrypt's `var s0 = BLOWFISH_S0_INIT` works (types.spl is a separate module).
The benchmark works around this by building the table with a `build_flag_table()`
function that returns a fresh local `[i64]` — the return copy is the table.
This is a separate interpreter bug worth tracking independently.

**Benchmark design limitation — results not directly shippable:** The benchmark
amortizes the `build_flag_table()` call across 128M lookups. In a real library
call (`is_space(ch)` called once per char), there is no amortization — each call
would need its own 256-element value-type copy, which is prohibitively expensive.
A shippable form would also require the `ch < 0 or ch >= 256` guard, putting a
branch back before every lookup and eliminating the composite advantage.
Therefore the LUT/Inline ratios below **measure the lookup kernel only** and
do not represent achievable library performance.

**Results (1M iters × 128 range, Cranelift native, single sample):**
C reference ran at 1k iters (different env-var name in C source); C ops/ms
numbers are noisy for fast functions — treat LUT/C ratios as approximate (±30%).

| Function   | C (ops/ms) | Inline (ops/ms) | LUT (ops/ms) | Inline/C | LUT/C  | LUT/Inline |
|------------|-----------|-----------------|--------------|----------|--------|------------|
| is_digit   | 1,855,072 |         765,399 |      416,120 |    0.41x | ≈0.22x |      0.54x |
| is_upper   | 1,580,246 |         960,405 |      404,456 |    0.61x | ≈0.26x |      0.42x |
| is_lower   | 1,280,000 |         670,571 |      381,107 |    0.52x | ≈0.30x |      0.57x |
| is_alpha   | 1,488,372 |         391,999 |      405,548 |    0.26x | ≈0.27x |      1.03x |
| is_alnum   | 2,206,896 |         260,580 |      338,022 |    0.12x | ≈0.15x |      1.30x |
| is_xdigit  | 1,066,666 |         261,199 |      397,856 |    0.24x | ≈0.37x |      1.52x |
| is_space   | 3,368,421 |         292,292 |      367,515 |    0.09x | ≈0.11x |      1.26x |
| to_lower   | 2,844,444 |         739,444 |      511,488 |    0.26x | ≈0.18x |      0.69x |
| to_upper   | 3,121,951 |         767,091 |      449,113 |    0.25x | ≈0.14x |      0.59x |

**Findings:**

- **Composite lookup kernel faster (is_alpha, is_alnum, is_xdigit, is_space):**
  The LUT kernel (array load + bitwise AND, no guard) is 1.03–1.52x faster than
  the inline branch-chain kernel. +25% for is_alnum, +52% for is_xdigit, +26%
  for is_space. This confirms Cranelift branch-chain lowering is the bottleneck
  for composite predicates — but only in the amortized kernel form.

- **Leaf functions regress (is_digit, is_upper, is_lower):** LUT 0.42–0.57x of
  inline. Array load + bitmasking costs more than two direct integer compares.
  The lookup overhead exceeds the branch savings for simple range checks.

- **to_lower / to_upper regress:** LUT 0.59–0.69x of inline. Array lookup plus
  one-time setup overhead exceeds simple conditional add/subtract.

- **Does not close the gap to C:** Even the best LUT result (is_xdigit ≈0.37x)
  falls far short of 0.5x C. C -O2 benefits from LTO, loop unrolling, and
  SIMD vectorization that no pure-Simple source change can replicate.

- **Not deployable as a library fix:** The benchmark's amortized setup and
  missing non-ASCII guard mean the measured gains do not translate to real
  `ctype.spl` function bodies. A shippable LUT would add per-call cost that
  erases the composite advantage.

- **Scope of fix:** The LUT experiment confirms that the pure-Simple source
  ceiling for problem #2 (composite branch-chain codegen) is ~1.5x over the
  current ctype.spl — still leaving is_space at 0.11x C. Problem #1
  (cross-module call overhead) is untouched. There is no pure-Simple path to
  the 0.5x C floor.

**Conclusion:** The lookup-table approach is a confirmed pure-Simple dead end.
The composite kernel improvement (22–52% over inline branch-chain in the
benchmark harness) is real but not shippable and does not close the gap to C.
`ctype.spl` is unchanged. The root cause remains Cranelift codegen quality and
absent cross-module inlining. No further pure-Simple source change is worth
pursuing here.

## 2026-05-29 Worker A Recheck

Scoped repair pass owned only ctype-related files/tests/docs and did not touch
Rust seed code.

Focused check:

```bash
SIMPLE_LIB=src bin/simple check src/lib/common/ctype.spl test/perf/ctype/bench_ctype.spl test/perf/ctype/bench_ctype_inline.spl test/perf/ctype/bench_ctype_lut.spl
```

Result: pass for all four files.

Warn-only cross-module benchmark:

```bash
SIMPLE_CTYPE_BENCH_SAMPLES=1 SIMPLE_CTYPE_BENCH_ENFORCE=0 bash test/perf/ctype/run_ctype_benchmarks.shs
```

Result: checksum parity passed, native ratios remained below the 0.50x floor
for every benchmark: `is_digit 0.26x`, `is_upper 0.28x`, `is_lower 0.37x`,
`is_alpha 0.28x`, `is_alnum 0.14x`, `is_xdigit 0.31x`, `is_space 0.10x`,
`to_lower 0.16x`, `to_upper 0.18x`.

Same-file and LUT recheck against a 1M-iteration C reference:

```bash
bin/simple native-build --entry test/perf/ctype/bench_ctype_inline.spl --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap -o build/perf/ctype/bench_ctype_inline
build/perf/ctype/bench_ctype_inline > build/perf/ctype/simple_inline.out
bin/simple native-build --entry test/perf/ctype/bench_ctype_lut.spl --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap -o build/perf/ctype/bench_ctype_lut
build/perf/ctype/bench_ctype_lut > build/perf/ctype/simple_lut.out
gcc -O2 -DITERS=1000000 -o build/perf/ctype/bench_ctype_ref_1m test/perf/ctype/bench_ctype_ref.c
build/perf/ctype/bench_ctype_ref_1m > build/perf/ctype/c_1m.out
```

Observed ratios:

| Function | Inline/C | LUT/C | LUT/Inline |
|----------|----------|-------|------------|
| is_digit | 0.47x | 0.23x | 0.48x |
| is_upper | 0.57x | 0.23x | 0.40x |
| is_lower | 0.51x | 0.32x | 0.62x |
| is_alpha | 0.28x | 0.30x | 1.09x |
| is_alnum | 0.17x | 0.22x | 1.30x |
| is_xdigit | 0.27x | 0.38x | 1.41x |
| is_space | 0.09x | 0.11x | 1.24x |
| to_lower | 0.28x | 0.18x | 0.66x |
| to_upper | 0.26x | 0.15x | 0.56x |

This confirms the earlier conclusion: the LUT kernel helps only composite
same-file kernels and still does not meet the 0.50x floor; it also regresses
leaf predicates and conversions. Because `std.common.ctype` already uses direct
range checks and a shippable table-based implementation would require per-call
setup/copy or a runtime/static-data fix plus bounds guards, no pure-Simple
library patch is justified. Remaining work is Rust-side/native-backend work,
outside this Worker A scope.

## 2026-05-29 Cranelift ctype Inline-Lowering Pass

Implemented a bounded Rust backend mitigation:

- `src/compiler_rust/compiler/src/codegen/instr/calls.rs` now lowers ctype
  predicate/conversion calls to direct Cranelift integer comparisons/selects.
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` routes
  imported `ctype.is_*`/`ctype.to_*` static method calls through that inliner.
- `test/perf/ctype/run_ctype_benchmarks.shs` gained
  `SIMPLE_CTYPE_BENCH_CLEAN=1` so enforced perf runs can avoid stale native
  object reuse.

Verification:

```bash
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
SIMPLE_LIB=src bin/simple check test/perf/ctype/bench_ctype.spl src/lib/common/ctype.spl
git diff --check
SIMPLE_CTYPE_BENCH_ENFORCE=1 SIMPLE_CTYPE_BENCH_CLEAN=1 SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src bash test/perf/ctype/run_ctype_benchmarks.shs
```

The enforced benchmark still fails the 0.50x floor, but the regression is
substantially narrowed compared to the prior cross-module run:

```text
is_digit 0.47x
is_upper 0.49x
is_lower 0.63x
is_alpha 0.48x
is_alnum 0.30x
is_xdigit 0.58x
is_space 0.19x
to_lower 0.39x
to_upper 0.41x
```

Disassembly confirms hot `ctype.is_digit` calls no longer call
`common__ctype__is_digit`; they lower to inline compare instructions. The
remaining misses are now branch/loop codegen quality against gcc `-O2`
(`is_alnum`, `is_space`, conversions), not cross-module call overhead alone.

## 2026-05-30 Pure-Simple Scope Recheck

Scoped pass owned only pure Simple ctype/perf files, focused benchmark docs,
`.spipe/pure_simple_ctype_perf_gap/**`, and this tracker. No Rust changes were
made.

`src/lib/common/ctype.spl` is still in the direct range-check form for all hot
predicates and conversions. The previous lookup-table experiment remains a
non-shippable benchmark-only kernel: it requires amortized table construction,
adds bounds guards for real library semantics, regresses leaf predicates and
conversions, and does not close the gap to the 0.50x C floor.

Focused check:

```bash
SIMPLE_LIB=src bin/simple check src/lib/common/ctype.spl test/perf/ctype/bench_ctype.spl test/perf/ctype/bench_ctype_inline.spl test/perf/ctype/bench_ctype_lut.spl
```

Result: pass for all four files.

Warn-only benchmark:

```bash
SIMPLE_CTYPE_BENCH_SAMPLES=1 SIMPLE_CTYPE_BENCH_ENFORCE=0 SIMPLE_CTYPE_BENCH_CLEAN=1 SIMPLE_LIB=src bash test/perf/ctype/run_ctype_benchmarks.shs
```

Result: checksum parity passed, native compilation succeeded, and native/C
ratios remained below the 0.50x floor for eight of nine entries:
`is_digit 0.39x`, `is_upper 0.40x`, `is_lower 0.53x`, `is_alpha 0.43x`,
`is_alnum 0.25x`, `is_xdigit 0.50x` (warned as below exact floor),
`is_space 0.15x`, `to_lower 0.41x`, `to_upper 0.25x`.

Conclusion for pure-Simple scope: no concrete shippable library mitigation is
available without changing backend/static-data/value-copy behavior. The bug
should remain open for native backend/codegen work; further `ctype.spl` churn is
not justified by the current evidence.

## 2026-05-30 Native Static-Data LUT Probe

Scoped pass worked in `/tmp/simple-ctype-perf` and owned only ctype/perf
benchmark evidence, `.spipe/pure_simple_ctype_perf_gap/**`, and this tracker.
No push was performed.

Hypothesis tested: move the 256-entry LUT into a separate module-level `val`
array so a guarded lookup-table ctype implementation can avoid the per-call
table construction/copy blocker from `bench_ctype_lut.spl`.

Added benchmark evidence:

- `test/perf/ctype/ctype_lut_tables.spl` — benchmark-local module-level
  `CTYPE_FLAG_TABLE`.
- `test/perf/ctype/bench_ctype_static_lut.spl` — guarded cross-module static
  LUT probe for composite predicates only. It exits nonzero when checksum
  validation fails, so the native static-data correctness blocker is visible to
  automation.

Focused checks:

```bash
SIMPLE_LIB=/tmp/simple-ctype-perf/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check test/perf/ctype/ctype_lut_tables.spl test/perf/ctype/bench_ctype_static_lut.spl
SIMPLE_LIB=/tmp/simple-ctype-perf/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check src/lib/common/ctype.spl test/perf/ctype/bench_ctype.spl test/perf/ctype/bench_ctype_inline.spl test/perf/ctype/bench_ctype_lut.spl
SIMPLE_LIB=/tmp/simple-ctype-perf/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple native-build --entry test/perf/ctype/bench_ctype_static_lut.spl --source src/lib --source test/perf/ctype --entry-closure --backend cranelift --runtime-bundle core-c-bootstrap -o build/perf/ctype/bench_ctype_static_lut
build/perf/ctype/bench_ctype_static_lut
SIMPLE_CTYPE_BENCH_SAMPLES=1 SIMPLE_CTYPE_BENCH_ENFORCE=0 SIMPLE_CTYPE_BENCH_CLEAN=1 SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple SIMPLE_LIB=/tmp/simple-ctype-perf/src bash test/perf/ctype/run_ctype_benchmarks.shs
git diff --check
```

Results:

- Static LUT check passed and native build succeeded.
- Native static LUT execution produced invalid checksums:
  `is_alpha expected=52000000 actual=128000000`,
  `is_alnum expected=62000000 actual=128000000`,
  `is_xdigit expected=22000000 actual=128000000`,
  `is_space expected=6000000 actual=0`; after the benchmark cleanup, this run
  returns `exit_code=1`.
- Current cross-module benchmark still misses the 0.50x native/C floor on eight
  entries: `is_digit 0.37x`, `is_upper 0.54x`, `is_lower 0.36x`,
  `is_alpha 0.25x`, `is_alnum 0.20x`, `is_xdigit 0.45x`,
  `is_space 0.16x`, `to_lower 0.21x`, `to_upper 0.25x`.
- `git diff --check` passed.

Conclusion: the static-data route is blocked by native correctness for
cross-module module-level array lookup before it can be considered as a ctype
performance fix. Do not apply the LUT to `src/lib/common/ctype.spl`; the next
action belongs in backend/global-array correctness and branch/loop codegen.
