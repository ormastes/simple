# `bin/simple run` demotes to hybrid-interp-splice and every list comprehension yields `[]`

**Status:** open (workaround in place)
**Severity:** P2
**Found:** 2026-11-04 while probing the AST traversal for the closure refactor engine

## Symptom
Under `bin/simple.exe run <file.spl>` the seed prints
`[engine-demotion] reason=hybrid-interp-splice detail=...` and afterwards every
list comprehension evaluates to an empty array: `[for x in xs: x]` -> `[]`,
`[for x in xs if c: x]` -> `[]`, and `[...].len()` on the inline form -> `-1`.
The same file under `bin/simple.exe test` or with
`SIMPLE_EXECUTION_MODE=interpret bin/simple.exe run` is correct.

Repro: `scratch cr_lc.spl` —
```
fn filt(xs: [i64]) -> [i64]:
    [for x in xs if x >= 0: x]
fn main() -> i64:
    print("{filt([3, -1, 7]).len()}")   # run: 0 ; interpret: 2
    0
```

## Impact
`compiler.core.ast_traversal.flat_stmt_child_exprs` ended in a filtered
comprehension, so under `run` every statement's child expressions were dropped
and every AST-walking lint rule silently saw no expressions.

## Workaround / fix
- `flat_stmt_child_exprs` now filters with an explicit loop.
- The closure-refactor harness child is spawned with
  `SIMPLE_EXECUTION_MODE=interpret` (`compiler.tools.fix.closure_runner`).
Related: `seed_list_comprehension_join_and_empty_native_2026_10_21`
(comprehensions lowering to nil on the native lane — same class, different engine).
