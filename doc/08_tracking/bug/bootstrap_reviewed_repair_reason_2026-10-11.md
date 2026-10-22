# Reviewed compiler repair admission reason

REQ-BOOTSTRAP-REVIEWED-REPAIR: a reviewed, unlanded compiler repair can request
Stage3 verification without claiming that the repair has landed or inventing a
seed defect. The typed reason is `verify-reviewed-compiler-fix`; Stage4 and
unknown reason names remain rejected.

The reason declares intent, not authenticated review. The existing planner
receipt continues binding exact parent, runtime, planner closure, executable,
source/git state and invocation identities. Existing admission verification
is unchanged. Include this source change before freezing the refreshed Stage2;
changing the planner after Stage2 would invalidate source provenance.

Validation: the shell policy regression passed and whitespace checks passed.
The typed Simple regression is prepared but UNRUN. The standalone Simple
planner must accept this reason while minting the actual identity-bound Stage3
receipt with the admitted refreshed Stage2; this remains a required execution
gate. No product PASS or release qualification is claimed by the shell test.
