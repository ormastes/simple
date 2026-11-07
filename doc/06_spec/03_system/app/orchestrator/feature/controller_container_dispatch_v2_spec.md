# Controller/container V2 packet and reply integrity

Status: **NOT_RUN — awaiting verification**. Authored from executable assertions;
not generated execution evidence, signed-authority PASS or runtime/provider proof.

Spec: `test/03_system/app/orchestrator/feature/controller_container_dispatch_v2_spec.spl`.
Fixture: `test/fixtures/orchestrator_acceptance/controller_container_dispatch_v2.spl`.
Authored labels ORCH-02/HOST-02 record intended assertion mapping pending existing
requirement reconciliation, not complete implementation/NFR coverage.

## Setup and proof limits

The fixture uses actual canonical assignment and host-reservation/receipt helpers,
plus actual Ed25519 signing functions through existing V2 message/digest codecs.
Four separate grant/approval pairs represent assignment, controller execution,
host preparation and host execution. Test seeds are deterministic TEST ONLY;
no publisher trust, current clock or SDK authorization is inferred from framing.

Linux body is produced by its real retained-request codec and semantic digest.
Windows body is explicitly opaque common-wire data, used only to exercise its
backend tag/service-incarnation scope. It does not qualify Windows provider
request semantics or Docker execution. Neither case opens an owner/provider.

## Eight scenarios and concrete checks

Each executable step repeats its case title exactly.

| Scenario | Steps and expected assertions |
|---|---|
| Preserve four real proof pairs | Roundtrip controller and host V2 packets for both backend tags. Retain distinct grant IDs, all approval signature bytes and exact nested execution body. |
| Full scope, UID and operation | Service-mode boot remains EMPTY; native machine is separate from physical alias. Intent fence equals the all-field scope hash. Reject changed host operation, coherently changed assignment UID, native machine, incarnation, physical alias or provider generation. |
| Renew proofs without semantic change | Generate new real-signed proof frames. Retained Linux body/semantic digest, canonical plan, assignment bytes and operation payload remain exact while proof signatures and whole packet change. Decode preserves the original body. This does not automatically authorize renewal. |
| Prepared receipt tamper | Reject altered prepared revision, receipt digest, receipt operation, immutable intent plan digest or forged nested receipt. A valid receipt is integrity data, not authenticated channel provenance. |
| Helper budget and unique operation | Roundtrip a helper tied to actual canonical parent budget/operation/assignment. Reject helper operation equal to parent, absent/empty budget digest and unsupported helper kind. Different budget digest or helper operation changes helper-plan hash. |
| Strict packet framing | Reject wrong version/kind/type, unknown fields, duplicate version, missing each proof frame and noncanonical trailing data; cover controller, host and helper decoders. |
| Correlated reply without false completion | Compare exact UID/host operation/assignment and nested response hash. Reject completionObserved=true or string false, wrong kind/version/target, altered host bytes without matching hash, completed status, duplicate version and noncanonical framing. |
| UTF-8 byte ceilings | Reject1048578-byte execution body and oversized2MiB packets, helper source beyond16KiB, nested host reply beyond128KiB and outer reply beyond256KiB. No truncation is permitted. |

Reply status host-prepared/runtime-observed records correlated facts only;
completionObserved is always false. The nested host response must still be decoded
and checked by the actual consumer against expected full runtime scope. A valid
hash alone is not native completion or producer authentication.

## Assertion mapping and mandatory integration gates

ORCH-02 maps to immutable controller/host operation and renewed-proof packet
identity, exact reply correlation and explicit false completion. HOST-02 maps to
full service/native scope, prepared receipt and helper parent/budget binding.

Host must verify each action's current signed grant AND human approval, validate
actual backend request semantics and account parent plus all helpers atomically
in the SAME physical ledger. A helper-plan budget digest is not budget approval;
the consumer must match the approved retained budget and existing parent.

No signed admission, protected root lookup, native boot attestation, parent
acceptance, ledger mutation, real app roundtrip or container lifecycle runs here.
Those remain root/host/platform gates through the actual Simple Container API,
with independent native ID/nonce inspection. No build, admitted SSpec, generated
manual, coverage or full-system PASS is claimed.
