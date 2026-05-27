# Short Grammar Placeholder Rejected In Parenthesized Pipe Callback

Date: 2026-05-27
Status: open

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

