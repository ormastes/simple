## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: fixed in .spl (2026-05-29) — root cause was the `parse_pipe()` function (line ~127) else-branch not applying `transform_placeholder_lambda` to the pipe RHS; a second identical pipe loop in the binary-expression context (line ~470) already had the fix applied. Fix: changed `expr_call(right,

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Short Grammar Placeholder Rejected In Parenthesized Pipe Callback

Date: 2026-05-27
Status: fixed in .spl (2026-05-29) — root cause was the `parse_pipe()` function (line ~127) else-branch not applying `transform_placeholder_lambda` to the pipe RHS; a second identical pipe loop in the binary-expression context (line ~470) already had the fix applied. Fix: changed `expr_call(right, [left], 0)` to `expr_call(transform_placeholder_lambda(right), [left], 0)` in `parse_pipe()`. Test `"pipe to placeholder lambda in parens"` in pipe_operator_spec.spl covers this. NOTE: bin/simple is the Rust seed binary — fix takes effect after self-hosted rebuild/bootstrap.

## Summary

The pipe operator accepts an explicit parenthesized lambda:

```spl
val result = 5 |> (\x: x * 3)
```

but rejects the equivalent placeholder callback:

```spl
val result = 5 |> (_1 * 3)
```

## Evidence

Changing `test/01_unit/compiler_core/parser/pipe_operator_spec.spl` from the
explicit lambda to the placeholder form produced one failing test in that spec.

`test/01_unit/compiler_core/parser/short_grammar_interpreter_spec.spl` confirms
that `|> &:len` works, so the gap appears specific to parenthesized placeholder
callbacks after the pipe operator.

## Impact

The short grammar fixer must not rewrite `|> (\x: x * 3)` to `|> (_1 * 3)`
until parser/runtime support is added.

