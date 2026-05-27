# Perf Bug: Pure Simple ctype 0.07x–0.46x C (Cranelift, no inlining)

**Date:** 2026-05-18
**Status:** Open — partially mitigated 2026-05-27; benchmark harness repaired,
ctype call nesting flattened, and MIR inlining now handles non-tail calls, but
native remains below the 0.50x C floor.
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
