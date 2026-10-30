# REQC004 does not cover `if val _ =` / `elif var _ =` wildcard bindings (2026-10-30)

Status: open
Area: compiler/35.semantics/lint/required_comment.spl

## Symptom

- `test/01_unit/compiler/lint/required_comment_admission_spec.spl`: 4 of 6 examples fail
  (`assert_true failed`).
- `test/01_unit/compiler/lint/required_comment_cli_spec.spl`: 2 of 10 examples fail ("emits REQC004
  through the production lint path for if val/var wildcard binding").

## Root cause

REQC004 is implemented only for `case _` match arms (`_check_match_arm`, `required_comment.spl:186`).
The admission gate `required_comment_source_may_match` (`required_comment.spl:26`) only admits
`pass_`, `todo(`, `case _` and dangerous keywords. No version of `required_comment.spl` in history
handles if/elif wildcard bindings or the `_("rationale")` binding form the spec uses. The spec is
ahead of the implementation; this is a missing feature, not a regression.

Supporting it needs:

- the walker to reach if-val/elif-var binding patterns in the arena AST (with a rationale accessor
  for `_("...")`)
- a token-aware admission check for `if`/`elif` + whitespace + `val`/`var` + `_`

## Unblock

Implement the if-binding branch of REQC004 and its admission token check. Then remove the `pending`
markers that link here.
