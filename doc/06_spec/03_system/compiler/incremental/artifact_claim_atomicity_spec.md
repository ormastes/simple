# Artifact claim admission

Requirement: [REQ-IM-007](../../../../02_requirements/feature/incremental_build_metadata_20261008.md).
Executable: [artifact_claim_atomicity_spec.spl](../../../../../test/03_system/compiler/incremental/artifact_claim_atomicity_spec.spl).

Status: authored manual; runtime and docgen UNRUN. This manual describes real
production bridge assertions, not a completed concurrency qualification.

## Dependency rejection and retry

1. Create two immutable actions, with B depending on A.
2. Request B before A completes. Observe `not-ready`, a queued service entry
   with no lease, and a pending coordinator entry with zero reserved memory.
3. Claim and complete A through the production bridge.
4. Retry B using a fresh token. Both service and coordinator must retain that
   fresh token; the rejected attempt must not supply publication authority.
5. Check that the original input route remains queued.

Before the repair, step 2 publishes the rejected lease, and step 4 inherits
`blocked-lease` instead of the caller's `retry-lease`.

## Memory pool rejection and retry

1. Claim A in a parse pool holding exactly one action's memory reservation.
2. Request independent B with sufficient caller memory but an occupied pool.
3. Observe `not-ready`, no lease for B, and A's unchanged lease.
4. Complete A and retry B. The returned owner token must be the new retry token.

## Existing foreign lease

1. Construct the split state possible after the old rejected-claim bug: the
   service has a lease while the coordinator remains pending.
2. Vary owner, token, and generation independently across three cases.
3. Attempt admission under the current caller identity. Observe
   `artifact-service-owner-mismatch`, unchanged service lease, pending
   coordinator state, and zero reservation.

## Duplicate accepted claim

1. Claim A and repeat its same-token claim.
2. Observe `single-flight` while both owner records retain the first token.
3. Complete A with its original authority. Observe a completed service entry
   containing the expected object identity.

## Qualification boundary

The four scenarios (including three mismatch inputs) exercise actual service,
coordinator, and bridge APIs sequentially. They do not establish process crash
reclamation, concurrent same-key publication, waiter bounds, scheduler liveness,
compiler startup, or any of the nine feature groups' overall completion.
Run under an admitted self-hosted SSpec runtime before reporting a behavioral
PASS; source inspection and the existing shell ownership guard are subordinate.
