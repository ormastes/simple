# Resolved-call receipt omits retained target context

The private `verification_capture_target_key_v1` included ten context fields but omitted build profile, subarch and CPU tier. Target-dependent lowering can read those fields; when final MIR/captures coincide, different contexts previously issued the same receipt. This is a source-confirmed identity omission, not a demonstrated incorrect binary or proof acceptance.

The fix shares the canonical thirteen-field length-framed payload with TargetHIR in `mir_target_context_identity_payload_v1`. TargetHIR v2 bytes remain unchanged; capture uses `C1-MIR-TARGET-v2`, intentionally changing every old capture receipt. The outer receipt schema remains unchanged because it hashes this versioned input. No persisted codec or validator contract changes.

Regression: actual frontend/HIR/direct-call lowering, closed manifest and site validation, repeat-context determinism, equal neutral MIR hashes with independent profile/subarch/tier receipt separation. Existing TargetHIR golden/all-field/delimiter fixtures remain applicable.

Runtime tests, bootstrap and performance checks: UNEXECUTED by user waiver. Source review is not native qualification. No other immutable-HIR rollout claim is made.
