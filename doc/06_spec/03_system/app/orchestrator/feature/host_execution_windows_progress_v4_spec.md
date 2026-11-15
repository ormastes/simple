# Cooperative signed host execution through a scripted Windows provider

Status: **AUTHORED_NOT_RUN**. No native Windows host, Docker engine, compiler,
test runner or documentation generator was executed.

Executable source: `test/03_system/app/orchestrator/feature/host_execution_windows_progress_v4_spec.spl`.
Fixture: `test/fixtures/orchestration/host_execution_windows_progress_v4.spl`.

The fixture uses actual Ed25519 signatures, signature verification, capacity
reservation, canonical shared operation journal and durable creation-intent
publication. Its journal is Linux-backed. Windows engine facts are explicitly
scripted responses checked by the actual Windows provider and portable
Container API. This does not qualify Windows storage, native command capture,
handle cleanup, engine effects or thread affinity.

REQ-HOST-WINDOWS-PROGRESS-001: commit execution before provider activity, prepare
before create, and durably retain the exact created identity before start.

REQ-HOST-WINDOWS-PROGRESS-002: cancellation or expired authority prevents new
launch submission and preserves the existing executing capacity charge.

REQ-HOST-WINDOWS-PROGRESS-003: a retired continuation cannot replay effects or
advance the canonical journal.

| Scenario | Observable assertions |
|---|---|
| Copied provider progress alias | Current owner plus old progress consumes engine then image once; retired alias returns blocked with cursor fixed at 2 |
| Existing finite execution API | Same 14 exact commands including prepare; running exact identity, retained created intent and unchanged executing charge |
| Complete cooperative execution | Cursor 0 after journal BEGIN; 2 after prepare; 7 after created inspection with durable exact intent; 14 after start and independent running inspection |
| Cancellation before create | Cursor stays 2, no creation intent, recovery required, executing charge remains |
| Approval expires between turns | At clock 9000, reject before create and preserve cursor 2 and charge |
| Retired continuation replay | Explicit retired error, cursor 0 and unchanged journal sequence |

Every progress loop is bounded to 64 turns and asserts its target cursor. The
command script validates exact argv and expected operation ordering. Capacity
is 4000 CPU millis and 1 GiB; the 2000 CPU millis / 512 MiB executing reservation
leaves exactly half available. Host identity, service fence, operation, signed
grant, approval and authority keys are consistent; they are not caller-provided
booleans bypassing verification. Startup performs actual scripted inventory
refresh and quarantine completion before execution.

One of the six scenarios exercises `host_authorized_execute_v2` directly, preserving
the finite Windows prepare/create/start/inspect sequence through the shared
provider reducer. It complements the four host cooperative scenarios and one
common provider alias scenario; no finite
command response is substituted for a native execution result.

The provider alias case exercises the real common execution-progress port and
canonical provider registry. It does not launch a child or qualify native
command cleanup, observation-marker authority or handle ownership.

No scenario claims native cleanup or absence proof. Source assertions and
signed scripted fixtures remain unqualified until an admitted runner executes
them; all native acceptance remains separate.
