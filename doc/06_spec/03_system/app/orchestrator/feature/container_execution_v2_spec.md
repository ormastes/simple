# Portable container execution V2 wire scenarios

Status: **NOT_RUN — awaiting verification**. Authored manual, not generated or
native provider evidence. Authored labels ORCH-02/HOST-02 await existing
requirement reconciliation; mapping below records intended assertions only.

Spec: `test/03_system/app/orchestrator/feature/container_execution_v2_spec.spl`.
Standalone diagnostic: `test/fixtures/orchestrator_acceptance/container_execution_v2.spl`.
No engine, files, provider or host authority is needed for these PURE assertions.

## Steps and expected observations

| Scenario | Real assertions |
|---|---|
| Both backend plans | Canonically encode/decode linux-podman and windows-docker-process; retain operation/generation and exact bytes. Digest equals SHA-256 of canonical plan; backend changes digest. |
| Invalid typed plans | Reject other backends, empty operation/boot, excessive service ID, nonpositive attempt/generation and malformed digest. |
| Strict plan syntax | Reject unknown authenticated field, string attempt, duplicate version, noncanonical trailing data and source beyond16KiB bytes. |
| Opaque request roundtrip | Preserve exact opaque body and backend through encode/decode/re-encode for both backends. This deliberately does NOT prove a valid provider request. |
| Invalid request wire | Reject supplied receipt, numeric body, wrong kind, corrupt plan, duplicate or missing fields and noncanonical framing. |
| Immutable plan digest | Valid changes to native boot/continuity, operation ID or request digest change the canonical plan digest. |
| Byte budgets | Accept exactly1MiB of multibyte body; reject more. Escaped1MiB quote body exceeds2MiB packet and fails without truncation. Reject oversized source/nested body. |
| Honest continuity | Roundtrip service incarnation with EMPTY boot, Windows colon-prefixed actual machine/owner IDs and separate authorized alias; reject whitespace/path/oversized native IDs. Roundtrip scope codec; changing alias, native machine, service, generation or owner nonce changes fence hash. Refuse invented service boot and mismatched native continuity ID. |

Native mode requires boot_id==continuity_id, both nonempty. Service mode's
continuity_id is data requiring a persistent owner; the wire decoder cannot
attest persistence. The current finite native API refuses service mode until its
explicit owner/quarantine exists. A weak boot counter is not native boot proof.

## Assertion mapping and limits

ORCH-02 maps to exact operation/backend/plan/request identity and canonical bytes.
HOST-02 maps to full scope binding, alias/native separation and bounded data.
The scope hash is only an opaque internal legacy fence, never an observed OS
boot. No parser success grants enrollment, continuity, signed authorization,
resource reservation or provider execution. No build, runtime, admitted SSpec,
SPipe/manual maintenance or full-system qualification is claimed.
