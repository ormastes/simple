# BUG: `text + i64` produces garbage in interpreter (seed) — use `.to_text()`

**Date:** 2026-06-15
**Status:** source fixed; focused seed-interpreter execution pending
**Severity:** Medium — silently corrupts string building; no error, just wrong output
**Found by:** search-custom-types AC-3 (Aho-Corasick) spec, while building canonical
sort keys with `"" + v`.

## Problem

Concatenating a `text` literal with an `i64` value via `+` returns garbage in the
interpreter (seed driver), instead of the decimal string of the integer.

```simple
fn i64_str(v: i64) -> text:
    "" + v          # WRONG: returns garbage

# A composite-key builder that should yield "3002006|1001004|2002004|"
# instead produced:
#   "0:0.0:<value:0x4>|nil:0.0:<value:0x6>|nil:nil:<value:0x4>|"
```

The corruption is value-position-dependent (`0`, `nil`, `0.0`, `<value:0xN>`),
suggesting the RHS `i64` is being read through the wrong tag / coercion path
rather than formatted as a number.

## Historical workaround (used in the spec)

Call `.to_text()` explicitly on the integer:

```simple
fn i64_str(v: i64) -> text:
    "" + v.to_text()   # CORRECT: "42", "3002006", etc.
```

`i64.to_text()` and `text + text` both worked correctly; only the implicit
`text + i64` coercion was broken in the original report.

## Reproduction

```simple
fn main():
    val v = 42
    print("" + v)            # garbage
    print("" + v.to_text())  # "42"  (correct)
```

Run with: `SIMPLE_BOOTSTRAP_DRIVER=$(ls -1 bin/release/*/simple_seed|head -1) bin/simple run repro.spl`

## Distinct from

- `any_plus_any_interpreter_native_divergence_2026-05-18.md` — that is ANY+ANY in
  *native* codegen emitting `iadd`. This is *typed* `text + i64` in the
  *interpreter*, which should route to string concat with a numeric format step
  but instead yields garbage.
- `rt_string_concat_quadratic_2026-06-12.md` — a perf issue, not correctness.

## Historical proposed fix

In the interpreter's `+` dispatch, when the LHS is `text` and the RHS is an
integer/`i64`, format the RHS via the same path as `.to_text()` before
concatenation, mirroring the documented interpreter rule that `1 + "x"` →
`"1x"`. The reverse (`"x" + 1`) appeared to misread the RHS payload.

## Resolution status (2026-07-15)

All normal interpreter binary expressions route through `eval_op_expr`. Its
text-left `+` branch now formats the right value with `to_display_string()`;
`i64` values therefore produce decimal text before concatenation. A focused
driver regression exercises the original `"" + v` form through
`Backend::Interpreter` and expects `42`. Execution remains pending a runnable
Rust test artifact, so no runtime PASS is claimed.
