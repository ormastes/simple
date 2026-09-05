# Short Grammar Placeholder Match Interpreter Failure

Date: 2026-05-27
Status: FIXED 2026-05-29

## Summary

Placeholder short grammar in a `match` selector was failing in the interpreter.
The root cause was that `Expr::Match` was missing from the Rust seed's
placeholder transform functions (`find_max_numbered`, `count_placeholders`,
`replace_placeholders`, `replace_numbered_placeholders`) in
`src/compiler_rust/parser/src/expressions/placeholder.rs`, and also from the
Simple self-hosted desugarer in
`src/compiler/10.frontend/desugar/placeholder_lambda.spl`.

## Fix

Added `Expr::Match` (Rust) / `EXPR_MATCH` (Simple) to all four traversal
functions in both implementations. The fix recurses into the scrutinee
(`subject` / `expr_left`) only — arms are a scoping boundary because `case _:`
uses `_` as a wildcard pattern, not a placeholder.

Two new test cases were added to
`test/01_unit/compiler_core/parser/short_grammar_interpreter_spec.spl`:
- "uses match expression as placeholder scrutinee in map"
- "uses match expression as placeholder scrutinee with wildcard default"

## Repro (was failing, now fixed)

```simple
val result = [1, 2, 3].map(match _1:
    case 1: 10
    case 2: 20
    case _: 30
)
```

## Impact

The lint fixer's guard (`if expr.starts_with("match "): return nil` in
`lint_short_grammar.spl`) is intentionally kept: the fixer's single-line
scanner cannot safely parse multi-line match bodies, so it must not auto-rewrite
`\value: match value:` to `match _1:`. Hand-written `match _1:` in call-arg
position now works correctly.
