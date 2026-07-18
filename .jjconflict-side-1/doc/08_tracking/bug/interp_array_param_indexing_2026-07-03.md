# Interpreter: array parameters break indexing — [[text]] params misparse, [f64] param variable-index reads 0

**Date:** 2026-07-03
**Severity:** high (silent wrong values / parse failure)
**Status:** open — workaround in use

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

Minimal repros for (1) and (2) in interpreter unit tests; likely the same
value-copy path as the Dict-in-struct corruption
([[interp_dict_in_struct_copy_corruption_2026-07-03]]) — parameter-passed
aggregates lose element addressing.
