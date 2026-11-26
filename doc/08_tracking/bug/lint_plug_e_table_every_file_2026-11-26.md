# Every `simple lint` run reports PLUG-E-TABLE (2026-11-26)

Status: verification-pending

## Symptom
Every file checked by `simple lint`, even an untouched one, reported
`PLUG-E-TABLE:not_dot_question`.

## Root cause
`run_admitted_static_lint_rule_table` (`src/compiler/90.tools/lint/static_rules.spl`)
requires the rule ids in the table to be strictly ascending, and it refuses any row
that breaks the order. In `static_lint_rule_table()`, `option_catchall` came before
`not_dot_question`. Since `"not_dot_question" < "option_catchall"`, the
`not_dot_question` row was refused on every unit. That rule also never ran.

## Fix
Put the rows back in sorted order (`not_dot_question`, then `option_catchall`).

## Regression test
`test/01_unit/compiler/lint/lint_rule_table_spec.spl`:
"keeps production rows strictly sorted so dispatch reports no PLUG-E-TABLE".
It runs the real production table and asserts that the errors list is empty.
Before the fix it failed (10/11 passing). After the fix all 11 pass.
