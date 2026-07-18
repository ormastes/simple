# `var (a, b) = (x, y)` tuple destructure — native `--entry` path

## Summary

The parser side (`parse_tuple_destructure_var` in
`src/compiler/10.frontend/core/parser_stmts.spl`) already had the
TOK_IDENT-capture-before-keyword-round-trip fix mirrored from the `val` form
at the pinned commit (`f88995e9d81a030fde96dd3310aeb5c8014f9703`) — no parser
change was needed. The gap was purely in HIR lowering:
`lower_hir_stmt_multi` (in `src/compiler/20.hir/hir_lowering/statements.spl`)
only special-cased `StmtKind.Val` whose encoded name starts with `"("`; a
`StmtKind.Var` with the same encoding fell through to `lower_hir_stmt`, which
has no tuple-destructure awareness, and the parenthesized joined name (e.g.
`"(a,b)"`) reached codegen as a single malformed identifier.

## Fix

Added a `Var`-tuple branch to `lower_hir_stmt_multi` and a new
`lower_hir_tuple_destructure_var` method that mirrors
`lower_hir_tuple_destructure_val` with two differences:
- `self.symbols.define(nm, SymbolKind.Variable, nil, span, false, true, nil)`
  — the mutable flag is `true` (val's is `false`), so each desugared binding
  is a real mutable local and `a = 5` reassignment works.
- Error messages say `var (...)` instead of `val (...)`, still carrying the
  mandatory `"unresolved name: "` prefix so `driver.spl`'s
  `_hir_lowering_error_is_fatal` promotes them to fatal build errors instead
  of a silently-downgraded warning.

Both the arity-mismatch and non-literal-initializer errors are loud
(non-zero exit, no binary emitted) exactly like the `val` form.

## Files touched

- `src/compiler/20.hir/hir_lowering/statements.spl` — only file changed.
  Diff at `scratchpad/var_destructure.patch` (66 lines).

## Battery (oracle vs native, values/order only — native print has no
newlines, exit codes are not meaningful per project convention)

All test programs use `fn main(): ...` (an explicit function body) — the
project's native `--entry` path only routes val/var-decl statements through
`parse_val_decl_stmt`/`parse_var_decl_stmt` inside a function body; bare
top-level script statements use a different, unrelated code path and are out
of scope for this fix (same as the already-landed `val` form).

| # | Program | Oracle (`bin/simple run`) | Native (`native-build --entry`) | Match |
|---|---------|---------------------------|----------------------------------|-------|
| 1 | `var (a,b)=(5,9); a=a+1; print(a); print(b)` (+ leading `print(0)`) | 0,6,9 | 0,6,9 | YES |
| 2 | `var (a,b,c)=(1+1,2*3,10-4)` (3-elem, expr inits) | 0,2,6,6 | 0,2,6,6 | YES |
| 3 | `var (a,b)=(1,2); a=a+10; b=b+20` (reassign both) | 0,11,22 | 0,11,22 | YES |
| 4 | `var (a,b)=make()` — non-literal init | 0,1,2 (interp allows it) | exit 1, **no binary**, HIR error: `unresolved name: tuple destructure "var (a,b) = ..." requires a literal tuple initializer...` | YES (loud-fail as designed; oracle interpreter path is unaffected/out of scope) |
| 5 | multi-construct: `var (a,b)=(1,2)`, `val (c,d)=(10,20)`, `while` mutating `a` 3x | 0,4,2,10,20 | 0,4,2,10,20 | YES |
| 6 | arity mismatch: `var (a,b,c)=(1,2)` | n/a | exit 1, **no binary**, HIR error: `unresolved name: tuple destructure arity mismatch for "var (a,b,c)": 3 name(s)...vs 2 value(s)...` | YES (loud-fail) |

Negative-verify performed empirically for both loud-fail cases: `echo $?`
after the `native-build` invocation itself (not a piped/tail exit code) was
`1` in both cases, and the target binary path did not exist
(`ls`/test confirmed no file).

## Full smoke matrix

`sh scripts/check/native-smoke-matrix.shs` result:

```
total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0
```

Only failure: `option_nil_check` (Option/nil check `x.?`), which is the one
pre-existing allowed failure per the task's gate criteria. All other 14
cases pass, 0 codegen fallback hits.

## Notes

- Worktree left clean after the run (`git diff` only shows the one file);
  no commit/push performed per instructions.
- Worktree removed with
  `git -C /home/ormastes/dev/pub/simple worktree remove --force /tmp/wt_vardes`.
