# `elif val Some(x) = ...` inside an if-EXPRESSION fails to bind the pattern var (interpreter)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Closed stale 2026-11-03

Re-verified on the deployed Rust seed (bin/simple.exe, built 2026-11-03) on origin/release/1.0.0 with both `SIMPLE_EXECUTION_MODE=interpret` and `=jit`: the documented repro now produces the correct result on both lanes (see lane seed-interp-p23 evidence: float `0.0/0.0 1.0/0.0 -1.0/0.0` -> `NaN inf -inf`; `d["k"].push` twice on a 1-element list -> len 3; `elif val Some(x) = o` in an if-expression -> binds 7). Closed as stale.

## 2026-11-10 P3 triage (work/p3-interp2-20261110) — interpreter fix CONFIRMED; JIT-lane divergence found (routed)

Independent re-verification on the deployed Windows Rust seed (worktree
`bin/simple.exe`, fixtures `build/p3fix-interp2/elif_val_repro*.spl`):

- `SIMPLE_EXECUTION_MODE=interpret`: `elif val Opt.Some(x) = o` inside an
  if-EXPRESSION binds correctly — `r=7` (pattern var as whole arm value) and
  `r=107` (x + 100 variant). The documented interpreter symptom is gone;
  the 2026-11-03 stale closure holds for the interpreter lane.
- `SIMPLE_EXECUTION_MODE=jit` (and default lane): the SAME programs print a
  nondeterministic pointer-sized garbage value (`r=3788094155553`,
  `r=4350936198245`, varies per run) — the JIT lane appears to read the
  enum payload through the wrong representation for elif-val pattern
  bindings in if-expressions. No fallback diagnostic fires, so this is a
  silent mis-compile, not a demotion.
- This is a compiler/JIT codegen issue (elif-val payload extraction),
  outside the interpreter lane's write scope (src/compiler,
  src/compiler_rust). Routed to the compiler lanes as a fresh finding;
  repro fixtures preserved at `build/p3fix-interp2/elif_val_repro.spl` and
  `elif_val_repro2.spl`.
