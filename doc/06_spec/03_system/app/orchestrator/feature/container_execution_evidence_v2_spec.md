# Container execution observation integrity

Status: **NOT_RUN — awaiting verification**. Authored manual, not generated
execution evidence, native absence proof or signed-host authorization PASS.

Spec: `test/03_system/app/orchestrator/feature/container_execution_evidence_v2_spec.spl`.
Boundary: `src/lib/common/contracts/container/execution_evidence_v2.spl`.
Authored labels ORCH-02/HOST-02 are assertion intent pending existing shorthand
requirement reconciliation; no full acceptance/NFR/coverage claim follows.

## Setup: constructed observations, never a native oracle

Every fixture is pure typed data. Linux uses podman and a native-boot-shaped
scope; Windows uses docker and an explicit service-incarnation-shaped scope with
EMPTY native boot. Physical host alias and actual-machine fields stay distinct.
The64-character native ID and opaque all-field scope fence are exact bytes.

Wait data contains a nonblank program and a full-ID argv vector, exited state and
workload exit23. Separate absence data models a full-ID container query with its
own query/observation digests and exact-native-object-absence-v1 proof kind. None
of these commands execute. Declaring this proof kind or a hex digest cannot
prove absence, continuity, producer authentication or capacity-release authority.

## Eight cases and exact step/check mapping

Each executable step uses its case title verbatim.

| Case | Required observations |
|---|---|
| Round trips both backends | Canonical absence and completion encode/decode/re-encode; retain full native ID, exit23, independent absence query digest and complete wait-observation digest. |
| Canonical query argv boundaries | Compare digest with independently canonicalized operation/program/argv. Different grouping, missing empty argument, program or action changes the digest. Embedded NUL argument is refused. |
| Every observation field | Independently change status/action/query, result exit/stdout/stderr/reason, state phase/exit/reason, then runtime native ID/UID/attempt/operation/generation/scope fence/engine; every digest changes. |
| Terminal wait instead of cached state | Refuse blank program, blocked/wrong action, wrong command action, stopped phase or negative workload exit. Reject tombstone proof kind and nonpositive absence time. |
| Full exact identity and binding | Refuse native ID shortened to63, altered scope fence, mismatched64-character native ID, UID/attempt/operation/generation, request digest, provider pin, physical alias or backend. |
| Service/native separation | Service boot remains EMPTY; alias differs from native identity. Equal-looking continuity IDs still hash differently by mode. Refuse unbound mode conversion or invented native boot. |
| Strict canonical wire | Refuse unknown fields, stringified integer values, duplicate version, noncanonical trailing bytes and a noncanonical nested runtime record; cover both completion and absence decoders. |
| UTF-8 bounds | Refuse per-argument and aggregate argv overflow, per-output and aggregate observation overflow, and65538-byte source beyond the64KiB evidence limit. |

The query fixture preserves exact typed command boundaries, including program
paths with spaces. It does not flatten argv into a shell command. Observation
hashes cover the actual supplied RuntimeOperation fields; no number alone is
interpreted as proof that an engine query succeeded.

## Assertion mapping and remaining native gate

ORCH-02 maps to exact execution/operation/request/observation integrity and
canonical replays. HOST-02 maps to complete scope/provider/native identity and
separate absence observation binding. No signature verification, host enrollment,
lifecycle operation, ledger mutation or parent acceptance is performed here.

Platform leaves must independently issue the exact full-ID native query, validate
its actual exit/output and preserve actual routed command/evidence hashes. A
local destroyed/tombstone state and an idempotent cached wait with blank command
cannot substitute for those observations. Signed host provenance, expected-parent
identity checks and authoritative absence remain mandatory before capacity is
released. Full platform API/native nonce/inspection suites belong to their owners.
No build, admitted SSpec, live query, SPipe/manual maintenance or runtime PASS is
claimed by this pure suite.
