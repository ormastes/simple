# `f64("x")` is 0.0 natively, a semantic error under the seed

- **Status:** open

`T(text)` conversion calls (HirExprKind.ConvertCall) lower a float target to
`rt_string_to_float` + `rt_value_as_float`, the same total recipe
`text.to_float()` uses: an unparsable text yields 0.0. The seed interpreter
raises `semantic: cannot parse 'x' as f64` for `f64("x")`. Parsable input is
identical (`f64("1.5")` 1.5, `float("42")` 42.0). The integer form has no
such gap: `i64("abc")` is 0 on both.

Also: `i8/i16/i32/u8(text)` parse natively but are `function not found`
under the seed interpreter, which only defines `i64`/`int`/`float`/`f64`
as callable conversions.
