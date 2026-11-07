# Protected daemon authority foundation V2

Base5854838c6124cfa9deb6c0d985814dd9db8bfe0e; isolated branch
`work/daemon-authority-foundation-20261107`. This change makes the existing
protected authority implementation available to non-Caret host owners. It does
not change the signed wire format or introduce another cryptographic algorithm.

## Provenance and exact scope

Copied only the two authorized unmerged main SDK modules. Both are byte-equivalent
to the release Caret implementations after replacing the snapshot's import with
the SDK grant-verification owner. No shared-tree compiler/database/orchestrator
changes or app facade edits were copied. Source originals:

| Main source | SHA-256 |
|---|---|
| src/lib/nogc_sync_mut/daemon_sdk/distributed_grant_verification_v2.spl | f307858e8fad092691e9d047c8efa35833cd5238aceaa695a1bb96a09be7762c |
| src/lib/nogc_sync_mut/daemon_sdk/distributed_authority_snapshot_v2.spl | 6045ef3c53c7b71a85a02e88eeed193d693f34c1afc2f18e00ad7e2b10463f58 |
| test/fixtures/app/llm_caret/distributed_authority_verification_fixture_v2.spl | 69ad9f0019a741131a0c156fb6e41f84d2d81ccbabe5600a0ae806f9c388db02 |
| test/01_unit/app/llm_caret/distributed_grant_verification_v2_spec.spl | 0f85432e9abdd45ed08c1d27c7143071d65cce312a425a790fc08633b8ad3237 |
| test/01_unit/app/llm_caret/distributed_authority_snapshot_v2_spec.spl | 277c2f88413fcf497a6209da4715a137cb0413ab745fb62da0cc31fe927575b5 |

The deterministic fixture and two specs are copied to daemon SDK test paths,
retargeting imports to the SDK nominal types. Existing app specs remain unchanged.
Concrete spec repairs replace unexpected-error branches with explicit `fail`
and import it; additional expiry/session/policy/revocation cases close gaps.
The two SDK implementation files remain exact copies of their main originals.

## Dependency closure and public surfaces

Exports: `DistributedAuthorityKeyV2`, grant/approval signature-message helpers,
`DistributedAuthoritySnapshotV2`, `distributed_authority_snapshot_create_v2`, and
`distributed_verify_grant_approval_from_snapshot_v2`. Existing direct verification,
key-check and lookup helpers are retained. No async facade is needed by the
agreed explicitly sync host consumer.

All non-SDK dependencies already exist at base: common distributed control and
authority types/codecs, builder identifiers/wire lines, SHA-256 and
`pure_ed25519_verify`. Tests additionally use existing pure Ed25519 signing from
deterministic public test seeds. No private service keys are read/stored here.
Golden signing messages are specified independently of the message builders.

## Security review

Grant signatures domain-separate `DBC_GRANT_SIGNATURE_V2`, issuer identity/key
revision and canonical encoded grant. Approval signatures independently bind
approver identity/key revision, canonical grant digest, canonical operation
digest, policy, session and expiry. SHA-256 binds payloads; it does not replace
Ed25519 signature verification. Both actual signature checks are mandatory.

Grant scope, environment, operation budget, policy, revocation and session are
checked against the exact operation. Issuer/approver keys must match protected
identity/role/revision/scope/budgets/current policy and epoch, remain live, and
have different public keys. Approval cannot outlive its grant; grant cannot
outlive either authority key. Snapshot publication bounds key/operation counts,
rejects duplicate live role/identity and invalid metadata, and builds an index.
Queries reject active-owner generation/policy/epoch mismatch before key lookup.

Trust boundary: snapshots and expected generation/policy/epoch/session come from
the protected service owner. Public mutable structs are not an authenticated
transport, opaque capability or unforgeable receipt. Client frames must never
supply the trusted snapshot/keys or expected-current owner values. Host owns
protected local policy loading and publication; this patch cannot authenticate
that loader. No caller boolean grants authority. No revocation freshness is
established without an owner-supplied current epoch. Dynamic buffers and pure
crypto are a cold reference path, not admitted allocation-free/hot-path timing.

## Evidence and limitations

Eighteen authored real-signature scenarios cover valid signed/decoded inputs,
issuer and approver tampering, payload replay, expiry, revoked/rotated/shared
keys, duplicate/foreign roles, missing keys and stale generation/policy/epoch/
session. Manual companions describe exact source oracles and remain NOT_RUN.
No tests/builds run in this lane; no native, timing, memory, admitted-SPipe,
cryptographic implementation audit, deployment or full-library PASS is claimed.
Root/Astra performs exact-head review before landing; host composition is separate.
