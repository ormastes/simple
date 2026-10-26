# Artifact claim atomicity

Requirement: REQ-ARTIFACT-CLAIM-ATOMICITY-001.

Manual derived from `test/01_unit/compiler/action_graph/artifact_claim_atomicity_spec.spl`.
Execution status: **UNRUN**. Astra cycle2 source-stage admission is not test evidence.

The fixture uses the production bridge, artifact service, persisted graph and
coordinator. It queues two 64-byte actions in a pool with one worker and a
1024-byte budget; the second depends on the first. No claim or commit owner is
replaced with a test implementation.

| Scenario | Trigger | Required observation |
|---|---|---|
| Successful targeted claim | Claim first with available memory 1024 | First claim succeeds; second remains queued without a lease. |
| Service memory denial | Claim first with available memory 32 | Service rejects; coordinator owner stays empty and reserved bytes stay zero; sibling stays queued. |
| Dependency denial | Claim second before first completes | Coordinator returns not-ready; both requests stay queued without leases. |
| Retry after dependency completion | Deny second, claim and commit first, retry second | Actual predecessor commit succeeds; second acquires its requested owner token. |
| Duplicate claim | Claim first, then claim first with another token | Duplicate returns single-flight; original service lease and coordinator owner remain intact. |
| Coordinator memory denial | Set pool budget 32; service available memory remains 1024 | Coordinator returns not-ready; no service lease or owner is published. |
| Cancellation | Cancel coordinator before claiming first | Claim returns cancelled; service remains queued without a lease. |

The source repair commits staged authorities only after both accept. Targeted
service staging uses one entry and reconstructs the outer queue without indexed
writes through copied storage. It does not repair general native struct-array
copying or prove single-flight across separate coordinator instances.

For qualification, execute this spec once per changed candidate using an admitted
producer/provider closure, retain individual case counts and diagnostics, and
compare the candidate's actual memory and timing with its baseline. Phase1-only
observations cannot establish pure-Simple/native correctness. Unsupported Phase1
features must be reported as skipped with a reason, never passed. Missing
exports, invalid artifacts or ambiguous provider identity prevent admission.

Source review: `build/native_probe/tldr-driver-batch-wiring-review-20261011-sol/astra-artifact-claim-atomicity-cycle2-review.md`.
Application identity: `build/native_probe/tldr-driver-batch-wiring-review-20261011-sol/ARTIFACT_CLAIM_LOCAL_APPLICATION.json`.
