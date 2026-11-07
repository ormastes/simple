# Distinct primary attach plan and archive

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 separate immutable plan domains; HOST-02 original helper binding.
Spec: `test/03_system/app/orchestrator/feature/container_primary_attach_v1_spec.spl`.

Setup: construct a full Linux primary workload/runtime/scope and typed daemon V3
planning template with zero dynamic transport generation/deadline. Intent semantics
are stdin enabled, signal proxy false, detach keys disabled, terminal mode stdin
or tty. The actual leaf must independently derive/check actual argv/config; this
pure plan is not a native observation or input-right grant. Build a real canonical
helper plan, original reservation intent, intent-hashed operation and matching
receipt using existing helpers. No signature or live owner is mocked.

| Exact step | Procedure / checks |
|---|---|
| round trips stdin and tty plans with full template identities and paired containment | Round-trip stdin and tty archives with paired containment hashes; preserve full template/runtime/parent identity and exact bytes. |
| separates primary attach from output follow digest and helper request domains | Equal common fields still produce distinct output-follow and primary digest domains. Structural primary helper matches; it cannot authorize output-follow domain. |
| retains the exact helper intent operation receipt fence resource chain | Refuse altered original intent nonce/plan hash, plan-hash-as-operation-payload, receipt revision, resources, scope, action and deadline rights. |
| refuses unsupported platform mode containment and generated planning fields | Refuse none/Windows, one-sided containment, generated transport/deadline and short native ID. |
| refuses stale digest unknown missing typed duplicate noncanonical and oversized archives | Refuse stale digest, unknown input-authority claim, missing containment field, wrong type, duplicate version, extra newline and over2MiB UTF-8 archive. |

Primary hash domain is container-primary-attach-plan-v1 and explicitly binds fixed
stdin/signal/detach semantics, terminal mode and both optional containment digests.
Empty containment is paired; otherwise both raw64 hashes are required. Archive
version1/kind container-primary-attach-plan stores every field and uses ONLY actual
daemon template encode/decode. Exact re-encoding and byte bounds validate integrity,
not live authority. Host requires a distinct retained archive and later typed
settlement; helper lease alone grants no Input/Geometry right.

ContainerHelperAssociationV3 extracts the exact corrected helper matcher. Caller
first computes its validated plan-domain digest. Output wrapper still computes
the original unchanged output digest/error and delegates; original matcher checks,
error strings/order and timeout relation remain intact. Full helper chain remains
helper-plan hash -> original intent.plan_digest -> canonical intent hash in BOTH
operation.payload_digest and reservation.payload_digest -> exact action-specific
receipt, scope/fence/generation/resources and attach-only deadline. No plan hash
is substituted as operation payload. Expiry is not a workload lifetime or cleanup
grant. Positive codec/matcher results are metadata only; no native primary attach,
stdin provider support, containment enforcement or authorization is claimed.
Builds/tests were prohibited; root/provider integration remains NOT_RUN.
