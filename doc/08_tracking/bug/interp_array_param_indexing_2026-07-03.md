# Interpreter: array parameters break indexing — [[text]] params misparse, [f64] param variable-index reads 0

**Date:** 2026-07-03
**Severity:** high (silent wrong values / parse failure)
**Status:** source-resolved; focused pure-Simple regressions added, execution pending

## Symptoms

1. **`[[text]]` parameter misparse:** a function taking a `[[text]]` parameter
   fails to parse/compile indexing or iteration over it, while the same code
   with a `[[f64]]` parameter works.
2. **Variable index on array parameter reads 0:** indexing an array passed as
   a function parameter with a *variable* index returns 0 in the interpreter
   (literal indices work). Found during MMULT/MINVERSE implementation.
3. Related, previously known: 2D index assignment `a[r][c] = v` is
   unsupported; flat 1D assignment works.

## Workaround (in production use)

`src/app/office/sheets/formula.spl` matrix ops (MMULT, MINVERSE, MDETERM,
MUNIT) are written fully inline: matrices stored as LOCAL flat row-major
`[f64]` arrays indexed `row*cols+col`; no struct or array crosses a call
boundary. Only scalar helpers (`_mat_abs`, `_mat_snap`) are factored out.

## Also reconfirmed

`grid` as a local variable name produces a misleading
`expected Colon, found Dot` parse error (existing bug doc
`parser_grid_identifier_keyword_collision_2026-07-03.md`).

## Next step

Run the focused cases in
`src/compiler/10.frontend/core/interpreter/test_interp.spl` once a permitted
pure-Simple verification binary is available. Static review on 2026-07-16
found that nested array types recurse through `parser_parse_type_impl`, array
arguments retain their value IDs in `eval_function_call`, and literal and
variable indices share `eval_index_expr`. The regressions cover both original
symptoms without relying on unsafe value extraction after a parse failure.

The earlier suspected Dict-in-struct copy path is unrelated: only value-type
struct parameters are copied, while arrays retain their value IDs. Nested 2D
assignment is also a separate backend-parity concern; the pure-Simple
interpreter already mutates the evaluated inner-array value ID and must not be
changed to compensate for a Rust-seed-only limitation.
