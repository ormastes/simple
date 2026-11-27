# Caret public controller metadata CLI acceptance

Status: **AUTHORED_UNRUN**. This manual is authored, not generated execution
evidence. No subprocess, native SSpec or producer admission PASS is claimed.

This checks the metadata subset of CARET-01, DAE-03 and OPS-01 through the actual
compiled Caret CLI and a separately compiled orchestrator. It establishes retained
intent and independent durable source observations only. It does not establish
execution authorization, authenticated remote services, live Podman, smux binding,
RUN behavior, runtime termination or full-system acceptance.

## Required environment

- `SIMPLE_CARET_ACCEPTANCE_BINARY`: absolute compiled public Caret executable.
- `SIMPLE_ORCHESTRATOR_ACCEPTANCE_BINARY`: absolute compiled controller executable.
- `SIMPLE_CARET_ACCEPTANCE_SHA256` and
  `SIMPLE_ORCHESTRATOR_ACCEPTANCE_SHA256`: exact binary hash pins.
- `SIMPLE_ORCHESTRATOR_ACCEPTANCE_ARTIFACT_ROOT`: absolute private evidence root.
- Source fixture `test/fixtures/orchestration/caret_agent_session.sdn`, supplied by
  the orchestrator composition lane.

Missing binaries, fixture, hashes or required capabilities fail/block the scenario;
they never cause a successful skip. Hash matching proves the selected binary's
identity, not producer admission. Record producer/source/runtime provenance
separately. Use the existing native AOT SSpec workflow with actual-execution
assertions, retained artifacts and disabled stub fallback. Interpreter loading is
not scenario execution.

## Primary scenario: retained intent survives a fresh public client

1. Open an isolated controller with explicitly pinned compiled binaries.
2. Submit one workload through the public Caret CLI, preserving the source path
   containing spaces as one argv value.
3. Inspect retained metadata through a fresh Caret process.
4. Require matching controller, request UID and source digest; confirmed retained
   intent must still report executionAuthorized=false, runtimeState=unobserved,
   terminationObserved=false and an unbound assignment.
5. Reopen the canonical generic DistributedOperationJournalV2 after the subprocesses
   exit and close its exact temporary writer lease before assertions. Require exactly
   one completed operation; decode its committed V2 envelope with the generic codec.
   Read the payload object by digest and independently parse raw metadata to match
   controllerId, workloadUid and sourceDigest. Read retained source and compare it
   byte for byte with the submitted source. This audit imports no product decoder
   or controller store and must not mutate CURRENT.

## Replay and refusal scenarios

| Scenario | Required observation |
| --- | --- |
| Identical request replay | Same stdout, unchanged durable CURRENT pointer and exact retained source |
| Changed valid source under the same UID | Exit 1, controller-error, confirmed=false, reconciliationRequired=true; original bytes and CURRENT unchanged; subsequent inspect succeeds |
| Wrong controller inspect | Exit 1, controller-error, original request UID preserved; original bytes and CURRENT unchanged |
| Relative controller executable | Exit 2, path-invalid, reconciliationRequired=false; no durable metadata change |
| Unexpected extra argument | Exit 2, usage-invalid, reconciliationRequired=false; no durable metadata change |

Each scenario initializes independent state. Refusals report status=unconfirmed;
wrong-controller inspection preserves the requested alternate controller identity,
and preflight/usage refusals preserve the original controller and request UID. Negative responses must retain
executionAuthorized=false. Subprocess stdout/stderr, argv, exit and artifact
observations are retained by the shared fixture under the configured evidence
root. The bounded raw CURRENT read is a durable mutation oracle, not proof of
power-loss durability or native runtime absence. Evidence paths are runtime
artifacts; no captures have been produced for this authored manual.

<details>
<summary>Executable SSpec and shared fixture</summary>

[Executable scenarios](../../../../../../test/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.spl)
use the production-connected helper at
`test/fixtures/orchestrator_acceptance/caret_controller_cli.spl`.
The helper performs real local-init and public Caret subprocess calls, retains
raw logs and checks receipt identity. It must never substitute scripted replies
or a constant-success result.

</details>
