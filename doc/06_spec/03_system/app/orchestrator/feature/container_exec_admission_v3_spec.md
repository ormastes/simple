# Nonserialized exec admission structural matching

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact immutable exec association; HOST-02 final effect boundary.
Spec: `test/03_system/app/orchestrator/feature/container_exec_admission_v3_spec.spl`.

Setup: construct a valid V3 exec request with full exact parent runtime CID and a
positive shared operation envelope. Construct the trusted-carrier shape with raw64
parent operation/assignment/provider/proof digests, canonical grant/issuer/approver
IDs, and an exact exec-only deadline. No decoder or signature verifier exists for
this carrier. No host journal, broker claim or provider is mocked.

| Exact step | Procedure / checks |
|---|---|
| matches exact request provider and live exec admission window | Accept exact expected request/provider and return900 then1 milliseconds remaining from the actual common deadline helper. This proves structural matching only. |
| refuses changed request nonce argv or exact parent container identity | Change nonce, argv or exact parent native CID in expected request; refuse each mismatch. |
| refuses operation id action payload host and malformed shared envelope | Change operation ID/action/payload/physical alias, or set invalid shared-envelope memory; refuse all. |
| refuses provider mismatch invalid retained digests and noncanonical proof identities | Refuse different/malformed provider pin, invalid parent/proof digests, empty grant, invalid issuer and overlong approver. |
| refuses widened actions stale deadline bindings expiry and unavailable clock | Refuse exec+attach widening, stale deadline operation/digest, exact-boundary expiry and negative clock. |

The actual host must verify signatures, match retained parent digests, establish
journal begin and hand the broker a verified live host lease. The broker must
acquire an exclusive same-operation claim before native exec creation. A copied
well-shaped carrier cannot provide either guarantee. Parent/proof digest fields
are format-validated here, not independently read from journals. The provider pin
is compared against the actual-owner expected baseline supplied by the consumer.
Deadline is a new-effect window only, never exec lifetime, PID stop, auto-kill or
capacity release. Running/unknown execs remain owned and charged after expiry or
disconnect. Builds/tests were prohibited for this source task.
