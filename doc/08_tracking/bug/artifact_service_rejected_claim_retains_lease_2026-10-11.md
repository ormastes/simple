# Rejected coordinator claim retains a service lease

Status: LOCAL_SOURCE_FIXED_TESTS_UNRUN. Bug DB reconciliation pending.

`demand_artifact_claim_v1` stages an artifact-service lease, then asks the build
coordinator to claim the same action. It publishes both staged owners even when
`claim.valid` is false. Dependency, pool-budget or cancellation rejection can
therefore leave a leased service request whose coordinator action never started.
This can strand a later retry. It is a source-established transition defect,
not a measured explanation of current host CPU utilization.

Repair: publish the staged service/coordinator only after both claims succeed;
on rejection return the existing claim/reason without publishing the lease.
Retain actual value-semantics/native array-copy qualification: staging must not
mutate the authoritative owner through aliases. This narrow source guard cannot
claim to repair the separately recorded native struct-array copy-isolation bug.

Actual-owner tests:
`test/01_unit/compiler/action_graph/artifact_claim_atomicity_spec.spl` checks
dependency rejection with both queues unchanged, retry after real predecessor
claim/commit, coordinator memory-budget rejection, duplicate rejection preserving
the existing admitted owner, cancellation rejection without a retained lease,
successful claiming preserving siblings, and service-side memory denial preserving
coordinator reservations. Tests are
UNRUN; no stubbed coordinator, service, hash or claim implementation is used.
Require an admitted provider closure, actual native ownership checks and Astra
review before runtime admission. No performance/memory improvement is claimed.

Astra cycle2 admitted exact source patch
`041b2f9515aba8dbd0a0c69ab29a15fc2e7081189cb5c51246283c5d379d09f4`.
Root applied it to the previously clean bridge and verified the exact candidate
postimage. Claim rejection now returns before publishing the staged lease;
the helper claims a one-entry service and rebuilds the outer queue with fresh
entries instead of indexed writes to copied queue storage. This fixes the
source transition and removes that staging alias path, but does not close the
native runtime copy defect or qualify memory/performance. No commit or remote
landing occurred. Application identity is recorded in
`build/native_probe/tldr-driver-batch-wiring-review-20261011-sol/ARTIFACT_CLAIM_LOCAL_APPLICATION.json`.
