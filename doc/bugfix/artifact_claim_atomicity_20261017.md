# Artifact claim admission publishes a rejected lease

Scope: REQ-IM-007 in `incremental_build_metadata_20261008.md`, async build
ownership row of the Phase3 incremental completion plan. Existing research,
architecture, and detail design remain authoritative; this is a focused defect
repair within their existing owner-transfer contract.

## Source finding

`demand_artifact_claim_v1` stages a service lease, then asks the action
coordinator to admit dependency/pool work. Before this change it publishes both
states even when `claim.valid` is false. The service can therefore remain leased
while the coordinator remains pending. A later retry looks up that old lease
and can pass its old token to the coordinator instead of the caller's token.

This finding is from source review, not a recorded runtime reproduction.

## Repair contract

Check returned service lease owner, lease ID, generation and cancellation
against the caller. Return `artifact-service-owner-mismatch` on mismatch.
Publish the staged service and coordinator only when both accept. Existing
success and duplicate-owner behavior retain their established interfaces.
No new owner, field, queue, death heuristic, or external process call is added.
The checks add constant work to the existing claim path; timing is unmeasured.

## Acceptance and review plan

`test/03_system/compiler/incremental/artifact_claim_atomicity_spec.spl` calls
the actual production bridge. Its mirrored manual describes dependency and
memory rejection, fresh-token retries, three identity mismatches, duplicate
claim preservation, and completion. No mock transition implementation is used.

Owner: Astra feature acceptance lane. Sidecars: N/A (bounded one-owner repair).
Merge owner and final reviewer: coordinating root agent. Runtime qualification,
generated-manual validation, and compiler/core/MCP smokes remain pending the
root's admitted producer and execution grant. No release PASS is claimed.

## Remaining feature gaps

All nine Phase3 feature groups remain unqualified. Existing object-reuse,
archive-observation, source-capture, SCC, source-change, and formal-model specs
must be preserved; they are not absent. In particular,
`bounded_dead_owner_claim_fixedpoint` still demonstrates missing artifact-service
dead-owner reclamation. Safe recovery requires trusted retirement evidence and
coordinated service/coordinator fencing; a newer caller generation alone cannot
prove owner death. This repair prevents a separate rejected-claim split state
and does not erase that counterexample or claim crash recovery.
