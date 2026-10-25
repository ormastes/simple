# Astra-guided release/1.0.0 fixup

Owner/merge owner: root. Guidance and final source review: gpt-6-astra.
Implementation sidecar: gpt-6-luna, bounded to five assigned files. Parent
independently accepts results and owns runtime evidence and PR landing.

Scope: preserve qualified return-owner/HIR metadata through arithmetic operator
calls and qualified layout metadata through borrowed Struct parameters. Preserve
Class reference semantics, no-copy borrowing, existing integer suffix policy,
upstream enum substitution, array initializer contextual checks and move rules.
The existing shared return owner is reused; its prior existence is not proof
that aggregate HirType transport works under the selected native producer.

Native helper names: check_cross_provider_operator_return,
mutate_borrowed_plain. Unit setup: imported_operator_lowering. Checkers:
imported_result_field_indices and imported_parameter_copy_widths. Step labels:
Preserve the declared provider of an arithmetic result; Borrow the exact provider
layout without copying it; Repeat provider checks with eager reversed registration.
The result checker follows one __sub__ result through binding provenance, then
requires exact ordered field indices0,1,2; parameter-copy reads are excluded.

Astra found and rejected the initial unfiltered GetField oracle. Luna corrected
it; Astra rereview found no remaining source blocker for these assigned changes.
No runtime PASS or merge approval follows from this source review.

Enum policy review: subject-owned bare variants retain subject identity and
unrelated/mutable names retain binding semantics (bootstrap_bare_enum_unit_patterns
contract). Integer suffix normalization operates on the existing Cast/IntLit
representation only; unknown/noninteger cases stay explicit. No new enum ABI,
flattened payload policy, permissive wildcard or bypass is introduced.

Verification order: unchanged native cases18–31 including exit22; new borrowed
mutation and cross-provider result cases32–34; targeted MIR/pattern/SCV specs;
exact compiler builds and executes Hello; Phase3 plus normal core/lib/MCP/LSP
and SPipe/manual checks; exact-head PR review including comments, then merge
against release/1.0.0. All verification is pending. No empty test exit is PASS.

The requested release tracking ref was stale because origin.fetch only mapped
release_phase3. Explicit refspec refresh identifies ba6f69adb99 as current target.
The reviewed patch is preserved before rebasing; rebase/target changes renew
applicable evidence rather than inheriting old green claims. Source recovery
and target migration do not reset the recorded cycle count or user exception.
