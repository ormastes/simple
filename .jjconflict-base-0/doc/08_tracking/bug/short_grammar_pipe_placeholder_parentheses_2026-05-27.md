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

Changing `test/unit/compiler_core/parser/pipe_operator_spec.spl` from the
explicit lambda to the placeholder form produced one failing test in that spec.

`test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl` confirms
that `|> &:len` works, so the gap appears specific to parenthesized placeholder
callbacks after the pipe operator.

## Impact

The short grammar fixer must not rewrite `|> (\x: x * 3)` to `|> (_1 * 3)`
until parser/runtime support is added.

