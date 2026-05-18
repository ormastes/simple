# Perf Bug: Pure Simple ctype 0.07x–0.46x C (Cranelift, no inlining)

**Date:** 2026-05-18
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
