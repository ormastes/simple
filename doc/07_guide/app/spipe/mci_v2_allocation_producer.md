# MCI-v2 Allocation Producer

Run `scripts/check/check-mci-v2-allocation.shs` with an evidence directory,
run/source/configuration identities, and capture/expiry nanosecond timestamps.
The default runner is the repository's canonical `bin/simple` release link; an
explicit runner must resolve under `bin/release/*/simple`.

Live launcher trust is deliberately not provisioned in source control. The
tracked `scripts/check/policy/mci-v2-allocation-launcher-trust.env` has
`scope=live`, `state=unprovisioned`, and no key ID, key path, or digest, so the
producer exits `BLOCKED` before executing the launcher. There is no interactive
or inferred approval path.

To provision live trust, a key custodian generates an Ed25519 signing key
outside the repository and gives only its PEM public key to the repository
maintainer. A named reviewer other than the custodian verifies the key origin,
intended allocation-launcher scope, key ID, and SHA-256 digest. The maintainer
then commits the public key and changes the policy to `state=provisioned`,
`algorithm=ed25519`, a unique `trusted_key_id`, the repository-relative public
key path, its lowercase SHA-256 digest, `review_status=approved`, and the
reviewer's stable ID. The reviewer also increments `policy_version` for any
trust-policy change, increments `revocation_epoch` when superseding trust, and
sets `min_build_epoch` to reject launchers built before the accepted baseline.
Review occurs through the normal code-review change; the
reviewer checks the digest independently and approves that exact policy diff.
The private key is never copied into the repository, evidence directory,
command line, policy, or receipt.

The launcher builder writes the canonical `mci-compiler-launcher-v1` receipt
with `attestation=signed-v1`, `algorithm=ed25519`, the policy key ID, and exact
policy version and revocation epoch, a unique build ID and monotonic build
epoch, capture/expiry nanosecond timestamps, and launcher source/binary SHA-256
values, then signs those exact receipt bytes into
a detached signature. Pass both files with `--compiler-launcher-receipt` and
`--compiler-launcher-signature`; the producer verifies the pinned key digest,
receipt bytes, key ID, policy/build floors, and Ed25519 signature before using
the launcher. The producer uses its run capture timestamp as the verification
instant and requires decimal timestamps satisfying
`launcher_captured <= verification_time <= launcher_valid_until`; both receipt
age and total validity are capped at 24 hours. Changing any receipt field
requires a new signature.

No consumed-receipt state is required: the attested launcher is immutable by
source and binary digest, its authority is bounded to 24 hours, and policy
version/revocation/build epochs can invalidate the entire prior class. This is
not a general replay exception; a per-run launcher must additionally bind its
run and configuration identities in a versioned receipt schema before use.

On success the producer writes
`artifacts/allocation-domain-arena-v1.evidence`, its content-addressed raw
`artifacts/allocation-domain-arena-v1.log`, and
`receipts/allocation.unsigned.template`, with the stable summary in
`allocation-report-v1.env`. The artifact binds the exact runner,
DomainArena spec and implementation hashes, raw-log hash, 12/12 scenario set,
sealed-profile snapshot, committed-state snapshot, and complete two-entry fault
ledger. An external signer must replace the signer placeholders, canonicalize
and hash the receipt, create `signatures/allocation.sig`, and publish it as
`receipts/allocation.receipt`. The producer intentionally never handles a
private key or claims a signed attestation.

Controlled fixture mode is only for the unit contract and requires
`MCI_ALLOCATION_CONTROLLED_FIXTURE=1`, both fixture files, and an explicitly
supplied `scope=fixture` policy. That test may create an ephemeral Ed25519 key;
the repository live policy never points to it. Its outputs say `CONTRACT_ONLY`
and are never eligible for aggregate release admission.
