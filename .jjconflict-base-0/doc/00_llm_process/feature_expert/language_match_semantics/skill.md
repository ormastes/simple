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
