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

## Summary
- Bug A: module-scope `for` -> flat AST bridge `unhandled expr node kind (tag=16)`.
- Bug B: module-scope `val _ = ...` -> `expected Ident, got _`.
- Workaround (both): wrap the script body in `fn main():` plus a trailing `main()`.
  A separate lane owns the parser fix; remove the wrappers only if that is wanted.

## Open defects found while verifying (failed BEFORE the wrap too)
Run with the fresh seed `simple run`; before and after wrapping give identical exit code and output.
1. `lint_cli_argument_count_contract_check.spl`: rc=1, `FAIL: argument-count lint escaped its CLI owner or missed a threshold`.
2. `lint_cli_duplicate_typed_args_contract_check.spl`: rc=1, `FAIL: DTYP001 CLI ownership, call line, or config parity changed`.
3. `lint_cli_wide_public_contract_check.spl`: rc=1, `FAIL: W0404 CLI parity changed ...`.
4. `lint_cli_collection_dtyp_contract_check.spl`: rc=1, `method len not found on type nil` at line 96.
These may be seed-interpreter limits rather than lint bugs; not triaged. The files only had to parse for this change.

## Perf regression (recorded per CLAUDE.md)
With all files parsing under the default `--source hir`, on the fresh seed (interpreted, shared box):
- `robust inventory --sdn test/01_unit/compiler/lint`: returned 0 (completed).
- `robust boundaries test/01_unit/compiler/lint`: did NOT finish within 1700 s.
- `simple test test/01_unit/compiler/lint/bound_origin_facts_spec.spl`: child-timeout at the 900 s budget, twice, with no verdict.
Todo: TODO(perf, P2): make the HIR walk of `test/01_unit/compiler/lint` fit the 900 s spec budget (profile `_robust_hir_facts` / `parse_full_frontend` + lowering per file, or narrow the spec to a small fixture dir); verify on a pure-Simple binary, since the seed is interpreted.
