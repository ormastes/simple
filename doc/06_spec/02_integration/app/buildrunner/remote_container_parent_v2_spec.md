# Remote container parent admission V2

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
test runner, provider, container, process or integration scenario was executed.

Source: `test/02_integration/app/buildrunner/remote_container_parent_v2_spec.spl`.
Fixture: `test/fixtures/buildrunner/remote_container_parent_v2.spl`.
Owners: `remote_container_session_v2.spl`, `remote_container_evidence_v2.spl`,
`remote_container_authority_v2.spl`, and the shared task/operation WAL owners.

When executed, the fixture writes real task/context/policy/toolchain/provider
pin and canonical container-request input files in a secure temporary directory.
Its task pins `remote-container/task_a.sdn` and
`remote-container-provider/task_a.sdn`; the latter contains the exact provider
digest and newline. It also pins `remote-workspace/task_a.nonce` as exactly
64 lowercase hex characters and a newline, and declares the probe output
`remote-workspace/task_a.probe.sdn`. The retained canonical receipt contains the
task identity, pinned nonce, and `write-read-delete` outcome. Successful fixtures
include those exact receipt bytes in the downloaded probe output; failure
fixtures retain the separate probe field with empty output inventories.
Task, operation, physical host and attempt match the common
execution plan. Original grant and human approval signatures use independently
constructed canonical messages with distinct deterministic test keys. The host
completion uses an independent golden V2 signing order. Context isolation is
`native-container`; completion time 1099 follows synthetic absence time 1000,
is no later than supplied current time 1100, and precedes authority expiry.

The common execution fixture uses the actual pure evidence constructor and
canonical query/observation digests over synthetic values. Its opaque request
body is hash-bound to the plan. It does not claim backend semantic decoding,
provider execution, native wait, actual absence or physical host attestation.
The synthetic engine-selected-user receipt matches the exact runtime, provider,
scope and request. Its time 990 precedes absence time 1000 and completion time
1099. Selected engine user `1000:1000` does not prove an effective UID or SID.
The signed execution digest hashes the canonical execution evidence, canonical
user receipt, and retained workspace receipt under the measurements domain frame.
No engine-user query or workspace access cycle was executed for this fixture.
The fixture compiler/runtime files are inert bytes and are never executed.

| Scenario | Intended assertion |
| --- | --- |
| Accepted wire and replay | The real parent adapter decodes the bundle, verifies signatures and bytes, writes exact binary output bytes, appends a typed Container record with canonical runtime/absence evidence, and commits the operation terminal digest. Release/reopen retains one task row and refuses the second completion. Native-only history rejects a fabricated PID downgrade. |
| Cancellation before admission | The actual operation WAL retains cancellation across reopen. A late completion rejects and writes no task row. |
| Output substitution | A host signature remains cryptographically valid over its unchanged original claims, but altered downloaded output bytes reject on independent parent hashing. Task history remains empty and operation remains executing. |
| User correlation | Canonically valid receipts for another native container, provider, scope, or an observation after absence reject against the exact execution identity without changing the original host signature or appending a task row. |
| Signed user bytes | A changed engine-selected-user string changes the measured execution digest and rejects against the original signed completion. |
| Workspace nonce and stale receipt | A changed nonce rejects its input pin; a receipt copied from another task attempt rejects its task identity. Original signatures remain unchanged and history remains empty. |
| Probe output agreement | Even after updating the result claim to match changed probe output bytes, the separately retained canonical receipt must match that output. |
| Workspace contract | Missing nonce input or undeclared probe output rejects before freezing evidence. |
| Failure measurements | An ordinary failure retains signed user/probe evidence, publishes no program/probe outputs, appends a typed failed record, and commits a failed operation. |
| Native frame rejection | A fully encoded structurally valid V1 native bundle is refused at the V2 container wire boundary without a task append. |
| Observation time | A freshly signed completion predating absence time rejects before task admission. |
| Output completeness | Unknown and missing downloaded outputs reject during pure evidence freezing. |
| Provider/plan pinning | Missing provider pin, changed observed provider, another execution attempt and a mutated unpinned container request reject independently. |

These specifications invoke the actual temporary-file task/operation journal
APIs and perform real publication/readback/reopen operations only when run;
they do not mock commits. Parent cancellation, exact original authorization,
current fences, signed bytes, request/provider pins and typed same-WAL history
remain mandatory. Signed synthetic observations do not become evidence of real
execution. Runtime, durability behavior and end-to-end provider qualification
remain unverified; no PASS or release claim is made.
