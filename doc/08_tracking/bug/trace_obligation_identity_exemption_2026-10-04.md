# Conflicting obligation identities could retain execution credit

Feature: simple_traceability_sdn_slop. Owner: root.
Status: source repair authored; runtime regression verification pending.

Source review of `src/lib/common/traceability/obligations.spl` found sequential
duplicate detection in the required-obligation branch only. A first eligible
required obligation could receive execution credit before a second obligation
with the same ID was encountered. If that second entry was NotApplicable,
the duplicate check was bypassed entirely and qualification could stay complete.
Empty-ID exemptions bypassed identity checking as well.

The repair counts all obligation identities before evaluation. Every conflicting
or unidentified entry is Incomplete and contributes neither structural nor
execution coverage; applicability cannot conceal the conflict. Three added
scenarios in `test/01_unit/lib/common/traceability/evidence_spec.spl` cover two
required duplicates, both orders of a required/exempt pair, and an empty-ID
exemption. These call the actual evaluator with otherwise eligible fixtures.

No pre-fix or post-fix runtime execution occurred: the admitted Phase 4 runtime
is still required. This is a source-level finding, not a claimed observed test
failure or verified fix. Close only after those regressions and the existing
qualification suite execute against the candidate; preserve actual receipts.

## Unreviewed applicability follow-up

Source review also found that a unique NotApplicable entry could exclude an
obligation with no reviewed policy decision. The evaluator now requires exactly
one independently admitted `TraceApplicabilityDecision` matching obligation,
requirement, criterion, test kind, subject, inputs, configuration and expectation.
Review identity and reason must be nonempty. Invalid graph/run binding prevents
exemption. Missing, stale, mismatched or duplicate decisions retain an incomplete
obligation in the denominator. Accepted exemptions receive no observation credit.

The evidence unit spec now exercises rejection and exact-review acceptance beside
a required acceptance obligation. This is authored, NOT RUN. Approval authenticity,
expiry and review-policy admission belong to the trusted adapter and are not
established by a nonempty review ID. That production adapter remains outstanding.
