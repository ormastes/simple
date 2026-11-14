# Language Match Semantics — Feature Expert

## Ownership

- Frontend patterns may preserve a bare identifier as a binding-shaped HIR
  node when its value/category is unavailable until MIR lowering.
- MIR must resolve immutable current-module scalar `val` names before enum or
  capture fallback. Mutable `var` names and genuinely unbound identifiers stay
  capture patterns.
- Dispatch must consume normalized arms. Integer-only cases retain the switch
  path; text and bool cases use ordered scalar equality, with text compared by
  content through `rt_text_eq_any`.

## Regression contract

`test/01_unit/compiler/codegen/match_bare_val_constant_spec.spl` is the exact
and adjacent contract: two text constants, two integer constants, bool values,
wildcard reachability, mutable-name capture, and genuine capture.

## Evidence honesty

Source and static contracts do not close native behavior. Require a
provenance-admitted pure-Simple CLI to execute the focused spec before changing
the BugDB row from verification-pending to fixed.

## Guards are evaluated on every arm shape (3a)

`case P if g:` runs its body only when `P` matches and `g` holds, for every
pattern kind. Two lowerings carry guards and both are counted:

- enum arms and guarded catch-alls: `lower_enum_match_flat`; guarded int /
  or-of-int / binding / wildcard arms: `lower_guarded_scalar_match`
  (`50.mir/_MirLoweringExpr/switch_operators_calls.spl`);
- tuple, text, range, struct and array arms: `build_if_chain`
  (`20.hir/hir_lowering/_Expressions/match_desugaring.spl`), which tests
  `pattern and { destructure prelude; guard }`.

The guard-count invariant (`E-HIR-MATCH-GUARD` / `E-MIR-MATCH-GUARD`, level via
`SIMPLE_MIR_VERIFY_LEVELS=E-MIR-MATCH-GUARD=...`) reports a guard that was parsed but
not lowered. Guide: `doc/07_guide/compiler/robustness/match-guard-invariant.md`.
Specs: `test/01_unit/compiler/50.mir/match_guard/`. The seed
`run` engine ignores a guard on `case _ if c:`; `simple test` evaluates it.

## A match with no matching arm fails (owner decision 2026-11-14)

Statement and expression form alike; an arm whose guard is false is not a
match. Record: `doc/08_tracking/bug/match_statement_no_arm_silent_noop_2026-11-14.md`.
Spec: `test/01_unit/compiler/control_flow/match_no_arm_fails_spec.spl`.

- Seed interpreter: `match_no_arm_error` (`interpreter_control.rs`), used by
  `exec_match_core`, both block-closure paths and the expression path.
- Seed JIT/native: the arm chain ends in `rt_panic` built by
  `match_exhausted_message` / `match_exhausted_panic` (`hir/lower/expr/control.rs`).
- Trap: that panic tail stands where a missing `else` used to be. Any analysis
  that asks "does this branch leave a value / of what type" must skip it with
  `HirExpr::is_match_exhausted_panic`, or a float merge slot is demoted to I64
  (value zeroed) and procedural bodies look value-returning.
- Not yet on this rule: the pure-Simple core interpreter (warn unless
  `critical`) and the self-hosted MIR lowering (warn-only for a non-total enum
  match). Do not write specs that pin a silent fall-through.
- Writing code: add the missing arm, or `case _: pass` with a comment when
  ignoring the rest is intended.
