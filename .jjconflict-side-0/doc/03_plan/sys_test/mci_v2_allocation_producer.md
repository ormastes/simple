# MCI-v2 Allocation Evidence Producer Test Plan

The allocation producer runs the focused `DomainArenaV1` unit spec exactly once
with a canonical self-hosted release binary. It admits the run only when all 12
named scenarios occur exactly once, the spec still contains exactly 12 scenario
definitions, and the frozen profile, committed-state snapshot, two-row ledger,
schema, run, source, and configuration contracts remain bound.

The controlled fixture test exercises successful collection, a missing marker,
a seed runner, fixture-mode authorization, the tracked unprovisioned live
policy, fixture-policy rejection in live mode, an invalid Ed25519 signature,
a mismatched public-key digest, and an unreviewed policy. Fixture output is always marked
`release_eligible=false` and `result=CONTRACT_ONLY`; it never publishes the
signed `allocation.receipt` consumed by the aggregate gate. The same canonical
run publishes a separate `mci-fault-injection-domain-arena-evidence-v1`
artifact and `fault-injection.unsigned.template`; allocation binds
`MCI-ALLOC-001..005` plus `MCI-NFR-007/008`, while fault injection binds only
`MCI-ALLOC-006` plus `MCI-NFR-009/010`. An external signer converts and signs
each receipt independently. The contract verifies that conversion and proves
that editing fixture policy fields invalidates its detached signature.

Expected outputs are `artifacts/allocation-domain-arena-v1.log`,
`artifacts/allocation-domain-arena-v1.evidence`,
`artifacts/fault-injection-domain-arena-v1.evidence`,
`receipts/allocation.unsigned.template`,
`receipts/fault-injection.unsigned.template`, and
`allocation-report-v1.env`. The producer owns both unsigned templates; the
aggregate owns signed-receipt parsing and the distinct scenario maps. Its
contract synthesizes live-shaped artifacts independently to prove exact
template-to-parser compatibility without relabeling controlled fixture output.

The production path fails closed for a runner outside `bin/release/*/simple`, a
seed authority string, unsafe paths, changed source/log snapshots, duplicated or
missing markers, stale schema/snapshot constants, and failed focused execution.
It also fails before launcher execution unless the tracked live policy pins a
review-approved Ed25519 public key ID/path/digest and the canonical launcher
receipt has a valid detached signature from that key. Provisioning is a reviewed
repository change containing only the public key and policy metadata; a private
key is never an input or artifact.
Validly re-signed negatives cover future capture, expiry, a validity window over
24 hours, a timestamp above signed-i64 maximum, an old policy version, a stale
revocation epoch, and a build below the policy minimum. The
canonical positive receipt binds policy version/revocation epoch, build ID/build
epoch, capture/expiry, key ID, and launcher source/binary digests. No consumed
state is needed for this immutable, digest-bound launcher because the 24-hour
window and policy epochs bound replay; any future per-run launcher schema must
also bind run and configuration hashes.
No compiler build, Engine2D check, or QEMU run belongs to this plan.
