# Stage4: lex_snapshot_restore corrupted indent stack — every `ident <` comparison failed

- **Status:** fixed
- **Date:** 2026-07-03
- **Component:** `src/compiler/10.frontend/core/lexer.spl` (`current_core_indent_stack_get/parse`)

## Symptom

Under the Rust seed interpreter, `parse_module` produced cascades of
`unexpected token in expression: Dedent` / `Error '    '` (whitespace Error
191 tokens) in ~all files containing an `ident < …` comparison.

## Minimal repro

```simple
fn f(a: [text]):
    var k = 0
    while k < 3:        # any `ident <` — if/while, int or ident rhs
        k = k + 1
```

`if k == 3:` parsed fine; `if k < 3:` derailed.

## Root cause

`ident <` triggers `try_skip_ident_generic_args()` (parser_expr.spl), which
speculates and backtracks via `lex_snapshot_save/restore`. Restore rebuilds
the CoreLexer indent stack with `current_core_indent_stack_parse`, which used
`part.to_int()` on `split(",")` elements. The seed interpreter misdispatches
`.to_int()` on split-produced strings (see companion seed bug md), returning
pointer-like garbage — the restored indent stack became `[<garbage>]`, so the
next indented line hit the `inconsistent indentation` (191) path and every
subsequent token derailed.

## Fix

Added `core_digits_to_i64` (dispatch-free digit parser using only string
`==` comparisons) and used it in `current_core_indent_stack_get` and
`current_core_indent_stack_parse`.
