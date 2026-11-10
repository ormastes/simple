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

## 2026-11-10 P3 seedfix lane — JIT ROOT CAUSE FOUND + FIXED (work/p3-seedfix-20261110, commit 752d38cd9875)

The interpreter-lane closure above stands. The JIT-lane divergence routed today is
FIXED in src/compiler_rust.

Root cause: `hir/lower/stmt_lowering.rs::build_pattern_binding_stmts` special-cased
ANY single-payload enum variant merely NAMED `Some` into a dual-representation If
(`rt_enum_id == OPTION_ENUM_ID -> rt_enum_payload`, else `rt_unwrap_or_self`) meant
for builtin Option / `T?` raw-migration values. A USER enum (`enum Opt: Some(i64) |
None`) has `rt_enum_id != OPTION_ENUM_ID`, so the else branch ran `rt_unwrap_or_self`,
which returns the WHOLE tagged enum word for a non-optional; the payload local then
held a tagged enum pointer read as a raw scalar — nondeterministic pointer garbage,
no diagnostic. match, if-val and elif-val-in-if-expression all share this binder, so
all three mis-computed on the JIT (confirmed: repro + isolation probes).

Fix: gate the dual form on the subject actually being an optional
(`optional_enum_payload_inner || types.optional_inner`); plain user enums use
`rt_enum_payload` like every other variant. Option<T>/T? keep the dual form.

Verified on a fresh build (debug AND release): repro now `r=7 r2=107` on the JIT
(was garbage), interpreter unchanged. No behavior change on
option_enum_match_variant / if_val_typed_option_class_unwrap / match_expr_binding_scope
specs. HIR-lowering regression test:
`cargo test -p simple-compiler --lib user_enum_some_variant` (passes; fails if the
gate is reverted — initializer becomes an `If`).
