# Container completion authority V2

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, tests, signer, container, or wire codec was executed to qualify
this artifact. No runtime PASS or coverage claim is made.

Source: `test/01_unit/app/buildrunner/remote_container_authority_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_authority_v2.spl`.

The V2 envelope carries explicit version 2, task/host/assignment/controller/
operation/request/grant bindings, measured result/execution/stdout/stderr/output/
test digests, signer identity and revision, completion time, and signature bytes.
Its signature domain is `SIMPLE_REMOTE_CONTAINER_COMPLETION_SIGNATURE_V2`; the
wire envelope domain is `SIMPLE_REMOTE_CONTAINER_COMPLETION_ENVELOPE_V2`.
It has no PID or native tree-reap field. Wire input is bounded to 16 KiB and uses
canonical shared scalars, bounded integers, and exactly 64 lowercase-hex encoded
signature bytes. Decode requires an exact encode round trip.

The protected parent must compute `execution_digest` from the canonical V2
measurements frame containing common `ContainerExecutionEvidenceV2`, the actual
engine-selected-user receipt and nonce-bound workspace probe. It validates
their container lifecycle/cleanup, exact runtime scope and immutable workspace
bindings and independently measures every expected digest.
The cryptographic verifier authenticates that binding and the original current
grant, approval, and host key. It does not inspect container runtime state or
grant lifecycle authority merely because a signature verifies.

| Scenario | Intended assertion |
| --- | --- |
| Golden signature and wire | Independently assembled V2 signing bytes match the production message; three-role fixture verification accepts; canonical wire round trip retains execution and log digests. |
| Signature mutation | Corrupted signature bytes reject; changed execution/stdout/output/test values reject cryptographically even when matching expected digests are also changed. |
| Parent observations | Each independently changed result, execution, stdout, stderr, output inventory, or test digest rejects against the original valid signed completion. |
| Current host authority | Revoked, rotated, wrong-role, and wrong-scope keys reject; reusing either issuer or approver public key for the host rejects. |
| Original signatures | Corrupted issuer and human-approval signatures reject. |
| Original task/request/grant | Changed task arguments, source, toolchain, inputs, outputs, attempt, request payload, or signed completion authorization digest rejects. |
| Parent fence and identity | Changed assignment/controller expectations and separately signed different host/operation claims reject. |
| Native V1 downgrade | Native completion signature bytes, native wire records, and an explicit version downgrade reject. |
| Current time/context | Future completion, expired grant or host key, and changed policy/revocation/session context reject. |
| Bounded canonical decode | Oversized, truncated, extra-field, leading-zero integer, malformed signature hex, and short-signature wire input reject. |

The shared authority fixture supplies deterministic original grant/approval/key/
task data. A separate test-only V2 signer assembles its own golden message.
Execution digest subjects in these crypto unit specs are opaque fixture inputs,
not fabricated canonical container records. Real execution evidence collection,
cleanup acceptance, journal publication, and container fault injection require
separate integration and runtime qualification.
