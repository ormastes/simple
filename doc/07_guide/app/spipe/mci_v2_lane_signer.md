# MCI-v2 non-review lane signer

`scripts/check/sign-mci-v2-lane.shs` is the canonical external-key signing
boundary for every non-review aggregate lane. It consumes the producer's exact
unsigned template and the already-published artifact, validates the lane's
producer class, scenario set, artifact schema, `live` mode, release eligibility,
artifact name, and SHA-256, then writes the aggregate's canonical field order.
It sets `attestation=signed-v1`, the operator-supplied key ID, the flat
`<lane>.sig` path, and the canonical receipt hash before detached signing.

The utility never generates, discovers, or exports a production key. Supply a
private key through a protected path owned by the external key custodian:

```sh
scripts/check/sign-mci-v2-lane.shs \
  --evidence build/evidence/mci-v2 \
  --lane tooling \
  --template build/evidence/mci-v2/receipts/tooling.unsigned.template \
  --artifact build/evidence/mci-v2/artifacts/tooling-generation-v1.tar \
  --private-key /protected/operator/mci-producer.pem \
  --trusted-key-id approved-producer-key-id
```

The evidence root and its `receipts` and `signatures` directories must be real,
operator-owned, non-group/world-writable directories. Publication is flat:
`receipts/<lane>.receipt` and `signatures/<lane>.sig`. Existing outputs are
never replaced. Both names are collision-preflighted; the detached signature is
published first and the admissible receipt last. Thus an interruption can leave
only a non-admissible signature, never an unsigned or partially written receipt.
The secure publisher uses no-follow opens, snapshots, fsync, and atomic
no-replace links.

Fixture, contract-only, blocked, wrong-schema, wrong-lane, malformed, reordered,
extra-field, hash-mismatched, or non-release inputs fail before publication.
The signer does not turn controlled fixtures into release evidence, and running
its contract does not claim a live release. The independent reviewer remains a
separate producer and is intentionally unsupported by this utility.

Run the focused contract once with:

```sh
sh test/01_unit/scripts/mci_v2_lane_signer_contract_test.shs
```
