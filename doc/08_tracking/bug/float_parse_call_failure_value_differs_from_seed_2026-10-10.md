# `f64("x")` is 0.0 natively, a semantic error under the seed

- **Status:** FIXED in the seed interpreter 2026-11-06 — see "Resolution"

`T(text)` conversion calls (HirExprKind.ConvertCall) lower a float target to
`rt_string_to_float` + `rt_value_as_float`, the same total recipe
`text.to_float()` uses: an unparsable text yields 0.0. The seed interpreter
raises `semantic: cannot parse 'x' as f64` for `f64("x")`. Parsable input is
identical (`f64("1.5")` 1.5, `float("42")` 42.0). The integer form has no
such gap: `i64("abc")` is 0 on both.

Also: `i8/i16/i32/u8(text)` parse natively but are `function not found`
under the seed interpreter, which only defines `i64`/`int`/`float`/`f64`
as callable conversions.

## Resolution (2026-11-06, seed interpreter)

`src/compiler_rust/compiler/src/interpreter_call/builtins.rs`:
- `f64(text)` / `float(text)`: `text.trim().parse::<f64>()`, 0.0 on failure
  — the `rt_string_to_float` + `rt_value_as_float` recipe — instead of
  `semantic: cannot parse 'x' as f64`.
- `i8/i16/i32/u8/u16/u32/u64(x)` (one positional argument): the value (text
  parsed with the same total `parse_int_lenient` as `i64(text)`) is cast to
  the width, matching native's `T(x)` -> `as T`. They were
  `function not found`. A user-defined function of the same name still
  wins (Priority-2 precedence rule).

Evidence: `test/fixtures/seed_interp/float_parse_conversion_call_repro.spl`,
`SIMPLE_EXECUTION_MODE=interpret`. Before (seed built from `ecb705896a4`):
`error: semantic: cannot parse 'x' as f64` (and, past that line,
``function `i32` not found``). After: `conv 0.0 1.5 5 7 9 200`.
Rust tests `interpreter_call::builtins::conversion_call_tests::{f64_of_unparsable_text_is_zero,narrow_int_conversion_calls_parse_and_wrap}`:
FAILED before (`cannot parse 'x' as f64`, ``function `i32` not found``), ok after.

Not in the interpreter lane: the seed JIT prints `conv 120.0 49.0 53 55 57 200`
for the same file (it converts the first character's code, not the parsed
text) — a separate seed JIT/codegen defect.
