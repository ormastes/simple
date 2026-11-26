# Top-level `for` and top-level `val _ =` fail the full frontend (2026-11-26)

Status: open (verification-pending workaround in tests)

Found while fixing `test/01_unit/compiler/lint/lint_cli_*_contract_check.spl`
(`simple robust --source hir` exited 2 on that directory).

1. A top-level (module scope) `for x in expr:` statement: the flat AST bridge
   reports `unhandled expr node kind (tag=16)` (EXPR_FOR) at end of file via
   `convert_nodes.spl` `convert_flat_expr`. Inside a `fn` body the same loop
   parses.
2. A top-level `val _ = call(...)`: `expected Ident, got _ '_'` (line 38 of
   `lint_cli_argument_count_contract_check.spl`). Inside a `fn` body
   (e.g. `src/app/browser/render_adapter.spl:270`) `val _ =` parses.

Workaround applied: each of the 8 contract-check scripts now wraps its body in
`fn main():` and calls `main()`. Fix needed: handle EXPR_FOR in the flat AST
bridge at module scope, and accept `_` as a binding at module scope.
