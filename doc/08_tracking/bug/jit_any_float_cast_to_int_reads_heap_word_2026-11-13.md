# Seed JIT: `any` holding a float cast to an int returns the box address

- **Filed:** 2026-11-13
- **Severity:** P2 (silent wrong value)
- **Status:** FIXED 2026-11-13
- **Area:** `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`
  (`lower_cast_expr`, the `any -> <int>` arm)
- **Reported by:** the ERR-01 lane,
  `pure_err01_untyped_local_of_optional_call_not_rejected_2026-11-13.md` ("on the
  seed JIT an `any` holding a FLOAT cast `as i64` yields a heap word").

## Symptom

Seed JIT (`SIMPLE_JIT_STRICT=1`) vs interpreter (`SIMPLE_EXECUTION_MODE=interpret`),
base `39d070a7eed`:

| expression (`v: any`) | JIT (base) | interpreter |
|---|---|---|
| `41.75 as i64` | 2582013624721 | 41 |
| `41.75 as i32` | 738279825 | 41 |
| `-7.5 as i64` | 2582013624977 | -7 |
| `(o ?? 0) as i64`, `o: any? = 41.75` | 2582013625073 | 41 |
| `o as i64` in `unsafe`, `o: any? = 41.75` | heap word | 41 |
| `41.75 as f64`, `42 as i64/i32/f64`, `true as i64` | correct | — |
| `(nil-any ?? 0) as i64` | 0 | 0 |

The number changes from run to run: it is the heap address of the float box.

## Root cause

`lower_cast_expr` lowers `v as <int>` with `v: any` as `UnboxInt` followed by
`Cast I64 -> <int>`. `UnboxInt` calls `rt_value_unbox_int`. That function
decodes tagged ints, true/false and wide ints, and returns every other value
VERBATIM. A float `any` is a heap-boxed `HeapFloat`, so the cast returned the
tagged pointer word. The float-target arm right above it already dispatched at
run time through `rt_any_mul(v, 1.0)`; the integer arm did not.

## Fix

The integer-target arm now calls `rt_any_to_int` instead of emitting
`UnboxInt`. That is an existing runtime function, registered for the JIT and
twinned in the C runtime (`runtime_native.c`). It truncates a float, and in
every other case it decodes the same way `rt_value_unbox_int` does. No new
runtime symbol, no change to `rt_value_unbox_int` / `rt_value_as_int` (which
have raw-untagged callers). Nil and `any` admission are unchanged: the cast is
still gated by `unsafe` / `??` exactly as before.

## Evidence

Spec: `src/compiler_rust/compiler/tests/any_float_cast_jit.rs` (6 tests).

| test | base | fixed |
|---|---|---|
| `any_float_as_i64_truncates` | FAIL (266287100006241) | pass |
| `any_negative_float_as_i32_truncates_toward_zero` | FAIL (3422651829) | pass |
| `unsafe_optional_any_float_as_i64_truncates` | FAIL (266287100143233) | pass |
| `generic_and_container_float_elements_as_i64_truncate` | FAIL | pass |
| `coalesced_optional_any_float_as_i64_truncates` | FAIL | pass |
| `any_int_and_bool_legs_unchanged` (control) | pass | pass |

## Still open (not changed by this fix)

- **Text in an `any`.** `"7" as i64`: interpreter 55 (code point); base JIT
  gave a heap word. With this fix it gives 7 (`rt_any_to_int` parses text). It
  still disagrees with the interpreter, but it is now stable. Note that the
  Rust `rt_string_to_int` is strict and the C twin uses lenient `strtoll`, so
  JIT and AOT can differ on input like `"4x2"`.
- **Narrowing out of range.** Both the typed float path and the `any` path
  truncate to i64 and then wrap, where the interpreter saturates per width:
  typed `f64 300.9 as u8` gives 44 on the JIT and 255 in the interpreter;
  `3000000000.5 as i32` gives -1294967296 vs 2147483647. Typed `-7.5 as u8`
  crashes the JIT (`fcvt_to_uint` trap). These problems were already there and
  are not specific to `any`.
- **Implicit any -> int slots.** `val n: i64 = v`, and passing `v` to an `i64`
  parameter, still go through `UnboxInt`, so a float `any` there yields the heap
  word. The interpreter keeps 41.75 in both places, with no conversion. These
  are not casts.
- **`u64` above `i64::MAX`** from a float `any` saturates at `i64::MAX`.
- **LLVM `Cast ANY -> int` arm** (`codegen/llvm/functions/casts.rs`) calls
  `rt_value_as_int`, whose non-text tail is a bare `>> 3`. Seed MIR no longer
  emits that shape for a non-literal `any`; it is reached only through
  `is_raw_literal_typed_any`.
- The pure-Simple MIR twin (`src/compiler/50.mir`) was not audited for the
  same shape.
