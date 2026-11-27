# TaskRef storage in the existing Controller journal

Status: **AUTHORED / NOT_RUN**. This is a manually authored companion to
`test/03_system/app/orchestrator/feature/controller_agent_task_objects_v1_spec.spl`;
no SPipe/docgen or actual-owner execution result is claimed.

Requirements: REQ-TASK, REQ-TASK-USE, REQ-TASK-REPLAY. The scenarios open the real
owned Controller journal in a private temporary directory, load the existing
AgentSession/catalog fixtures, and close through the actual retained cleanup
turn. No positive IO test fabricates a journal, lease, policy owner or Host.

| Scenario | Expected assertion |
| --- | --- |
| Retain, bind and restart | Exact retention/use retries do not advance the journal. Content cannot materialize before committed use. Raw bytes remain unchanged after owned close/reopen/replay. |
| Reject attempt substitution | Changed model, Host scope, raw version, namespace, TaskRef, source or catalog cannot replace an existing Controller/session/attempt. Original stored content remains readable under the exact binding. |
| Retain multiple versions | Two bodies under one logical reference remain distinct. Earlier use keeps its raw version. A second attempt can reuse it; a separately pinned later attempt can use the other version. |
| Require stored parents | Missing task, object publication without journal commit, absent pinned policy and missing desired session fail. Caller-provided digests do not supply stored authority. |
| Recover pending metadata | Actual admitted task and use operations complete through the existing owned journal projection. No second database/journal is opened. |
| Preserve cancellation history | A task use committed before parent cancellation replays. Current use/materialization fail after cancellation. Historical internal reads do not erase evidence or imply current client access. |
| Detect corruption | Modified committed object bytes fail read and exact retain retry. The API does not silently repair stored evidence from caller data. The test restores its own temporary fixture before cleanup. |
| Retain advanced owner on error | With an actual ten-event journal bound, use admission succeeds at event ten and begin fails. `ControllerTaskStoreTurnV1` returns that actual advanced journal and same lease with an error and `effect_attempted=true`. |
| Reject invalid terminal outcomes | Wrong completed digest and failed task metadata cause actual-owner projection rejection. Cleanup retains the actual last returned journal. |

The new store functions are trusted internal mechanisms. The service must verify
independent signed retain permission before retention, and fresh installed access
permission before **every** use/materialization. The storage spec does not test
expiry/revocation/signers or claim authorization coverage. The upper service
owner is responsible for that separate gate and for never exposing raw prompt
bytes in public receipts.

The replay implementation reads actual stored desired/policy/task parents,
checks canonical object/envelope/outcome equality, and builds one owner-scoped
history batch for task-use replay. Parent completion must precede use admission;
earlier cancellation forbids that use, while later cancellation remains valid
history. Hot use/materialize calls use indexed journal reads and do not rebuild
WAL history. Initial fixtures target the existing Linux owned storage port;
Windows retained-store integration is not exercised by these tests.

No runtime, native build, full AgentSession, provider start, workspace, terminal,
performance, branch coverage or release evidence is claimed. Failed primitive
operations that return no updated journal preserve the latest known owner;
the service must retain it and follow existing recovery/cleanup semantics.
