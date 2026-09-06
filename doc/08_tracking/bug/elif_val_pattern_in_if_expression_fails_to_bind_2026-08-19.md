# `elif val Some(x) = ...` inside an if-EXPRESSION fails to bind the pattern var (interpreter)

- **ID:** `elif_val_pattern_in_if_expression_fails_to_bind_2026-08-19`
- Status: OPEN (workaround landed)
- **Found:** 2026-08-19 (gui triage during the match-arm leak investigation)

## Symptom

Under the interpreter, an `elif val Some(x) = expr:` branch used inside an
if-EXPRESSION (value position) takes the branch but does not bind `x` — the
body then fails with variable-not-found or operates on a stale outer value.

## Workaround

Landed in `src/lib/editor/render/md_renderer.spl` — reproduce the original
shape from that file's git diff. The workaround restructures the `elif val`
into a statement-position `if val`.

## Suspected mechanism

Sibling of the match-arm binding family fixed in
`engine2d_factory_returns_dict_under_test_runner_2026-08-19` (five sites, last
being the `interpreter/expr/control.rs` match-expression write-back). The
if-EXPRESSION path (`eval_control_expr`, `Expr::If` with `optional_let_binding`
elif branches) needs the same treatment: bind into the branch env, mark
block-local, and never write pattern bindings back.

## Next steps

- Minimal failing-pre-fix repro spec (from the md_renderer diff shape).
- Fix in `interpreter/expr/control.rs` elif-branch handling; then revert the
  md_renderer workaround.
