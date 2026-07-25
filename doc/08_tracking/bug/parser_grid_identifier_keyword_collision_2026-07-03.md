# Bug: `grid` unusable as a local variable name — parser keyword collision

**Date:** 2026-07-03
**Severity:** medium (misleading diagnostics)
**Status:** source fixed in Rust parser 2026-07-15; focused execution pending

## Symptom
`val grid = some_call(x)` fails to parse with `Unexpected token: expected
Colon, found RParen` — the parser treats `grid` as the UI-layout contextual
keyword and expects `grid:`. The error location/message gives no hint the
identifier is the problem.

## Repro
```
fn f() -> text: "x"
fn main() -> i64:
    val grid = f()   # parse error: expected Colon, found RParen
    0
```
Renaming `grid` to any other identifier fixes it.

## Expected
Contextual keywords should only be recognized in their layout context, or the
diagnostic should say the identifier collides with a keyword.

## Resolution

`grid` remains a lexer token for the literal grammar, but expression dispatch
now selects that grammar only before `:` or `device`. Otherwise the token is an
ordinary identifier. Declaration patterns already accepted it, and the
pure-Simple lexer already treated it contextually. Focused execution is pending.
