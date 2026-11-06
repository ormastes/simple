# Seed JIT: `f64("x")` is 120.0 and `i32("5")` is 53 — the conversion call used the `as` cast

- **Status:** FIXED 2026-11-06 (branch `work/seed-jit-batch3-20261106`)
- **Found:** 2026-11-06, follow-up of
  `float_parse_call_failure_value_differs_from_seed_2026-10-10.md` (the
  interpreter half of that record is fixed by PR #7240).
- **Engine:** Rust seed HIR lowering, so the Cranelift JIT (`jit`, default
  `run`) and the seed LLVM backend both.

## Symptom

`test/fixtures/seed_interp/float_parse_conversion_call_repro.spl`:

```simple
val bad = f64("x")
print("conv " + bad.to_text() + " " + f64("1.5").to_text() + " " + i32("5").to_text() + " " + i8("7").to_text() + " " + i16("9").to_text() + " " + u8("200").to_text())
```

`SIMPLE_EXECUTION_MODE=jit` and default `run`: `conv 120.0 49.0 53 55 57 200`.
Expected (native contract, interpreter after PR #7240): `conv 0.0 1.5 5 7 9 200`.

## Root cause

`src/compiler_rust/compiler/src/hir/lower/expr/calls.rs`
`lower_utility_builtin` lowered the conversion CALL `T(x)` to exactly the
same `HirExprKind::Cast` as `x as T`. For a text source the Cast's rule is the
single-character code point (interpreter `interpreter/expr/casting.rs`
`cast_to_numeric`; Cranelift `codegen/instr/basic_ops.rs` `compile_cast`
loads the first byte), so the call form converted the first character's code
instead of parsing: `"x"` -> 120, `"1.5"` -> 49, `"5"` -> 53. `u8("200")`
looked right only by accident of the int Cast decode path.

## Resolution

For a text argument and a numeric target, `T(text)` now lowers to the parse
method the text receiver already uses — `text.to_f64()`
(`rt_string_to_float` + `rt_value_as_float`, 0.0 on failure) or
`text.to_int()` (`rt_string_to_int`, 0 on failure) — followed by a narrowing
Cast to `T` when `T` is not `f64`/`i64`. `x as T` is unchanged and keeps the
code-point rule.

Narrow-int audit: `i8/i16/i32/u8/u16/u32/u64/i64(text)` all had the same
defect (code point, then narrow) and are fixed by the same change. Numeric
arguments (`i8(300)` -> 44) were already correct and still take the Cast.
Remaining known divergence, not changed here: `rt_string_to_int` is strict on
trailing garbage (`"12x"` -> 0) while the interpreter's `parse_int_lenient`
takes the leading digits (`"12x"` -> 12); see
`to_int_contract_split_char_codepoint_vs_text_parse_2026-10-05.md`.

Evidence (debug seed from `release/1.0.0` @ `a58d06d80d3`):

| lane | before | after |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=jit` | `conv 120.0 49.0 53 55 57 200` | `conv 0.0 1.5 5 7 9 200` |
| default `run` | `conv 120.0 49.0 53 55 57 200` | `conv 0.0 1.5 5 7 9 200` |
| `SIMPLE_EXECUTION_MODE=interpret` | `semantic: cannot parse 'x' as f64` | unchanged on this base; `conv 0.0 1.5 5 7 9 200` with PR #7240 |

Rust tests `compiler/tests/conversion_call_text_parse_jit.rs`:
`f64_call_of_unparsable_text_is_zero` (returned 1 before, 0 after),
`narrow_int_conversion_calls_parse_text_and_wrap` (541 before, 277 after),
`as_cast_of_single_char_text_keeps_code_point` (ok before and after — pins
that `as` keeps its rule).
