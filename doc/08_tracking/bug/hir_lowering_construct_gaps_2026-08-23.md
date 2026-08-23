# HIR lowering emits Error/Any nodes for well-formed programs (6 construct gaps)

- **Filed:** 2026-08-23
- **Status:** OPEN
- **Layer:** `src/compiler/20.hir/hir_lowering/**`
- **Found by:** AST -> HIR construct census, `doc/09_report/hir_construct_coverage_matrix_2026-08-23.md`
- **Red spec:** `test/01_unit/compiler/hir/hir_lowering_construct_gaps_spec.spl` (6/6 failing, by design)

## Summary

Running the real lowering path (`parse_full_frontend` -> `hirlowering_for_module` ->
`lower_module`) over a battery of minimal well-formed programs and walking the resulting
HIR with the generated visitor shows six constructs that lower into `HirTypeKind.Error`,
`HirExprKind.Error`, or a silently erased `HirTypeKind.Any`.

This is the same defect CLASS that produced this session's stage1 failures
(`unresolved type: HirModule`; `String` 84 / `Option` 63 / `int` 62 unresolved). Those
took 3+ hour builds to surface because nothing asserted at the HIR boundary that a valid
program lowers without Error nodes. Each of the six below is detectable in seconds.

## The six

| # | source | emitted | expected |
|---|---|---|---|
| 1 | `fn f() -> never:` | `HirTypeKind.Error` | `HirTypeKind.Never` |
| 2 | `fn f(g: fn(i64) -> i64)` | `HirTypeKind.Any` | `HirTypeKind.Function` |
| 3 | `match e:` / `case A(v):` on `enum E: A(v: i64)` | binder typed `HirTypeKind.Error` | `HirTypeKind.Int` |
| 4 | `match x:` / `case [a, b]:` on `[i64]` | `HirExprKind.Error` | no Error node |
| 5 | `val s = #{1, 2}` | `HirTypeKind.Error` + `NilLit` | `HirExprKind.SetLit` |
| 6 | `fn f() -> i64!:` / `throw "bad"` | `HirExprKind.Error` | `HirExprKind.Throw` |

Cases 1, 2 and 5 additionally mean the registry variants `HirTypeKind.Never`,
`HirTypeKind.Function` and `HirExprKind.SetLit` are UNREACHABLE from source: they are
declared in `spec/compiler_schema/registry/`, carried through `hir_*_to_mir` transition
tables, and never constructed by any lowering arm.

## Reproduce

```
bin/simple test test/01_unit/compiler/hir/hir_lowering_construct_gaps_spec.spl
# expect: Results: 6 total, 0 passed, 6 failed
```

## Do not

Do not weaken the spec to match current output. The spec asserts the correct behaviour.
