# Production build action ownership

Executable: [build_cache_service_refinement_spec.spl](../../../../test/00_formal_verification/compiler/build_cache_service_refinement_spec.spl).

Status: authored manual; executable SPipe/docgen have not run. The separately
retained Phase 1 source replay reproduced the two service regressions and passed
their private fix plus eight controls. That evidence is narrower than this spec
and does not qualify a self-hosted or native build.

1. Claim an immutable action and keep the coordinator's returned owner state.
   A second owner receives `single-flight`. A foreign completion preserves the
   live claim; its actual owner completes and releases its memory reservation.
2. Submit action B's artifact with action A's lease. Nothing publishes and the
   original owner still completes A.
3. Deliver a late completion from an older owner generation. The current lease
   and generation remain intact; current-owner publication succeeds.
4. Repeat a claim against the returned service state. Exactly one queue entry
   and the original lease remain.

The producer invokes actual `coordinator_claim_v1`, `coordinator_commit_v1` and
`artifact_service_complete_v1`. It does not substitute a scheduler model. The
contract assumes callers serialize and retain one authoritative state; it does
not establish global deduplication across independent service instances.

Evidence/report: [formal verification report](../../../09_report/build_cache_formal_verification_2026-10-10.md).
Regenerate through the admitted `spipe-docgen` before claiming zero-stub manual
admission. Missing executable evidence is not a passing or skipped scenario.
