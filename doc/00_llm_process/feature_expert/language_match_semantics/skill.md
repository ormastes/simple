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
Specs: `test/01_unit/compiler/50.mir/match_guard/`. The seed interpreter
ignores a guard on `case _ if c:`; do not use it as the oracle for that shape.
