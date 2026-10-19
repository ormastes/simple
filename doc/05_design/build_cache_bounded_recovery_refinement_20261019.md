# Bounded cache recovery refinement

Owner: `/root/astra_warning_authority_review`; base `2fbe9ac8548`; branch
`work/formal-cache-recovery-refinement-20261019`. Reuses the clean authority
worktree; `work/managed-warning-authority-v2-20261019` and `a409d6f2e60` remain
retained. Sidecars N/A; independent oracle reviewer
`/root/higher_model_coverage_review`; merge owner root. This is a specification
extension in the selected nine-group scope, not another bootstrap attempt.

The original formal file tests the service alone. Production recovery already
exists in `artifact_owner_recovery.spl`; selected filesystem-backed recovery
scenarios already exist. The missing artifact is bounded comparison of an
independent abstract recovery model with the combined service/coordinator owner.
No production implementation changes are proposed.

## Domain and transition oracle

One action, 1,024 reserved bytes, pool capacity 2,048, generations 7 and 8,
distinct retained owner and lease identities. Initial state is a successful real
generation-7 `demand_artifact_claim_owned_v1` dispatch. Enumerate all 5^4 = 625
event words, checking their 2,500 prefixes independently.

| Event | Admitted transition | Otherwise |
|---|---|---|
| Recover8 | Running generation 7, no cancellation → queued; retain lease 7 as tombstone, select route owner/generation 8, release reservation | Reject, unchanged |
| Claim8 | Queued, no cancellation → running generation 8 with new lease and reservation | Reject, unchanged |
| Complete7/8 | Running matching generation, no cancellation → completed with artifact, succeeded coordinator/result, zero reservation | Reject, unchanged |
| Cancel | Set coordinator cancellation latch; running → cancelled service while coordinator retains running token/reservation; queued → cancelled service/coordinator; completed remains published | Repeated cancellation retains state |

The model is computed before invoking production and never reads production
outputs. Projection compares service and runtime states, cancellation latch,
request/action/snapshot identity, route successor authority, retained lease and
cancelled bit, owner token, artifact digest, reserved bytes and result presence.
The one-action domain makes the checked reservation also the entire pool's
reserved total. Count publications from actual state changes, at most one
overall; count starts at most once per generation. Preserve the earlier no-reap
claim fixed point, which remains a valid counterexample to unconditional progress.
Check each previous input projection after the owner returns a new route.
The explicit `&mut` cancellation API is excluded from that immutability claim;
it has no acceptance boolean, so check its state/latch transition separately.
Retain the original dispatch lease before enumeration; completion events never
borrow or relabel the currently installed lease as old authority.

## Exact production boundary

`DemandArtifactRouteV1` is constructed by `demand_artifact_route_v1` and advanced
through `demand_artifact_claim_owned_v1`, `demand_artifact_commit_owned_v1`,
`demand_artifact_cancel_v1` and `demand_artifact_requeue_retired_v1`. Retirement
calls the existing internal serialized parent transition only under the explicit
assumption that the parent has already admitted the exact old tree-reap proof.
No synthetic receipt, PID flag, clock expiry or fabricated process death enters
the model. The collector `demand_artifact_recover_owner_v1` and live broker are
outside this pure refinement domain.

## Falsifiability and evidence

Expected failures include accepting a stale completion, erasing a completed
artifact on cancellation, permitting a second generation-8 claim, losing the
retired lease fence, changing caller-retained inputs, and releasing a running
reservation merely on cancellation. Three separate projection mutation negatives
must detect changed lease generation, unearned publication and missing memory.

Traceability: REQ-FORMAL-BOUNDED, REQ-FORMAL-OWNER, REQ-IM-007 in
`test/00_formal_verification/compiler/build_cache_bounded_model_spec.spl`; manual
`doc/06_spec/00_formal_verification/compiler/build_cache_bounded_model_spec.md`.
Status **AUTHORED_UNRUN**. No interpreter, compiler, tests, docgen, builds or
process launches are authorized in this lane. Independent static review precedes
the frozen commit. Root owns later execution under an admitted resource envelope.

This does not prove multi-action fairness, arbitrary epochs/trace depth, live
process retirement, durable journal replay, filesystem source read-set
completeness, semantic compiler refinement or measured cost. It cannot promote
`FormalStatus` to a universal proof/refinement/artifact-admission state, mark the
entire nine-group feature complete, or admit Phase 3.
