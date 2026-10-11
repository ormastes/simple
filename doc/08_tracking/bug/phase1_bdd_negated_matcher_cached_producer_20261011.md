# BUG-PHASE1-BDD-NEGATED-MATCHERS-20261011

Status: OPEN. Owner: compiler/interpreter matcher surface. Native admission: pending.

The immutable Windows bootstrap producer with SHA-256
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`
executes the unchanged direct grammar regression
`test/01_unit/compiler/bdd_negated_matcher_chain_lowering_spec.spl` with four
examples, one passing and three failing. `.not.to_contain` accesses `not` on
String; argument-free `.to_be_nil` accesses a field on nil;
`.to_not_be_nil` leaves an unconsumed expectation. Direct syntax is preserved.
The historical backlog contains eighteen runs with the not-on-String signature.
The current pure interpreter field-access owners also lack interception for
these matcher links; the cached diagnostic does not qualify those owners.

Fourteen authorized consumer specifications temporarily preserve the exact
negative predicate as `expect(subject.contains(fragment)).to_equal(false)`.
Each carries this bug ID in an `@workaround` tag. The original subject and
fragment are unchanged; positive checks and all direct grammar regressions
remain intact. Remove these tags only when the canonical surface is fixed and
qualified, and then restore consumer matcher syntax through a separate review.

The real-file control reads the unchanged direct grammar regression and checks
both present and absent fragments. It passes one example. An isolated mutation
inverting the absent-fragment expectation to true fails with
`expected false to equal true`, one executed example and exit 1. Thus the
fallback predicate consumes a real expectation and detects inversion.

Evidence is retained under `build/phase1-negated-matcher-20261011/` in the
shared workspace: baseline.log, consumer-map.json, per-spec logs, results.json,
and inversion.log. Collection is one bounded diagnostic pass per identity.
Further source-contract failures are retained without weakening their checks.
No compiler rebuild, direct grammar rewrite, skip, or native/JIT admission.

## Completed independent source-contract slice

Five consumer specifications are admitted separately from the broader draft:
LLVM adapter trace, LLVM object-path lifetime, MIR text signature, query AST
projection, and query closure index. Eight previously failing criteria passed
after correcting literal interpolation and aligning exact fragments with
verified current owner boundaries, retained target configuration, group-qualified
lookup, and original function span provenance. Six unchanged earlier passing
criteria are retained without replay, giving incremental coverage of fourteen
criteria. No full-suite rerun or native qualification is claimed.

The other nine consumer workarounds and genuine coverage, MIR trace, performance
lint, and raw-SFFI snapshot defects remain open in the broader draft PR3015.
The direct matcher grammar defect remains OPEN.

The completed slice merged through PR3023
(`f3eb9e8a4c8a35f1de265062c3e804dd08a666f0`). The broader PR3015
preserves the remaining workarounds and ten open product-contract failures.
