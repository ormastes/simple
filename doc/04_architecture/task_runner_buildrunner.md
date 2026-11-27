# Shared TaskRunner and BuildRunner

Status: implementation draft, native verification pending. User-selected scope is a shared build/test task runner, grouped execution by default, adaptive isolation after attributable crashes, temporary durable task history and cheap commit snapshots. No running source or cache is changed by this candidate.

## Authoritative owners and compatibility

The existing app.bootstrap_builder.manager owns deterministic parent state and validates DAGs, reaped workers, exact identity and output hashes before success. Its implementation is extracted once to std.common.task_runner.scheduler. Existing BuildTaskV1/BuildRunV1 wire contracts and journal schema remain compatible; BuildRunner exposes the state as BuildRunnerV1. Old manager imports and portable/Windows/Linux executable entries are explicit compatibility facades. Windows JobObject and Linux cgroup ownership stay in their platform adapters.

The existing test runner has its own registration, per-case result, execution and database owners. Tests must reuse shared scheduling/recovery/storage contracts while retaining registered positive-case evidence. A listed test or zero exit code alone cannot create a passing attempt. An adapter maps native per-case receipts into shared frozen messages after validation.

## Shared interface

TaskRunnerIdentityV1 binds kind, task/case ID, backend, phase, producer/source/runtime/toolchain/policy/execution digests. Execution identity hashes arguments, relevant environment, fixture/config and schema; raw secrets never enter the journal. TaskRunnerAttemptV1 records identity, group, attempt, mode, PID and generation, outcome/reason, process exit/signal and separate task exit, reaped-tree fact, parent result-validation fact and log/result digests.

The identity function returns Result<text,text>. Execution-mode lookup consumes a bounded indexed history for one identity and returns grouped or isolated; a known exact-identity confirmed crash starts isolated. Recovery consumes the expected ordered ledger and validated attempts, confirmed group-crash and reaped facts, current attempt and maximum attempts. It returns passed/failed/isolated/exhausted/aborted identity lists. Ordinary compile/assertion failures are terminal, never retried merely for failure. Timeout, cancellation, invalid admission and transport uncertainty remain distinct aborts. Missing tasks may be retried only after confirmed group crash and complete tree closure.

## Group and process boundaries

Normal workers execute grouped work within their allotted threads. After a crash, only unknown work is isolated in fresh private attempt roots; proven independent passes and ordinary failures remain. Preserve first-crash logs and generation. For compiler SCCs, progress inside an uncommitted SCC is diagnostic evidence, not successful SCC publication. Isolated probes identify the culprit, then the affected SCC must rebuild under original atomic commit/loader rules. No singleton diagnostic can forge package admission.

Default requested budget is 80 jobs; resource admission and frontend concurrency limits remain separate. The parent owns mutable scheduler/index/journal state. Children receive frozen encoded requests and return frozen observations. No concurrent writer may publish CURRENT; process generation and lease prevent PID reuse or stale result delivery from releasing a live slot.

## Temporary DB and commit snapshots

Reuse the existing Simple text database or pure-Simple SQLite implementation selected by the storage owner; do not introduce another database engine. Its transactional task-history interface may reference content-addressed immutable payload/index pages. A commit manifest references its parent, source authority, last sequence, segment root and index root. An unchanged commit references the same objects; an updated row writes its record and bounded index path, never a full DB copy. Bound records, segments, pending results and cache pages; stream committed replay. Reuse validated no-replace publication primitives, not SCV helpers that ignore write results. This storage API is being reviewed independently before integration.

## Acceptance and ownership

Required tests: ordinary early failure followed by all independent jobs; validated cached success retained; aggregate failure preserved; grouped crash with known pass and unknown work; no retry before complete reap; known crash starts isolated; bounded exhaustion; timeout/cancel/admission abort distinguished; exact 80-worker budget; all expected ledger rows classified. Native build/test receipts and snapshot crash injection, tamper, stale lease and write-cost/RSS measurements remain required before qualification.

The current recovery fixtures are unexecuted; image selector shell syntax and scoped whitespace checks passed. Actual process fault injection and persisted-history integration remain pending.

Shared interface/manual step names: step("Admit exact task identities"), step("Run grouped tasks"), step("Preserve terminal evidence"), step("Isolate unknown crashed work"), step("Commit immutable task snapshot"). Any unimplemented acceptance assertion must fail explicitly; no placeholder passes.

Common runner/build adapter owner: phase3_snapshot_fix. Test adapter owner: astra_phase2. Snapshot implementation/review: cranelift_phase2 via root coordination. Lower-model sidecars: N/A; exact source/evidence reviewed by normal/high-capability agents. Merge owner/final reviewer: root. Existing policy checkpoint7bd8534ff3f stays separate. No native PASS or release admission is claimed.

The recovery `group_id` names one stable retry window, including grouped and isolated attempts. Each physical child has its own PID/generation; it must not change the recovery window. A fresh invocation has a fresh window. Persistent history feeds only initial execution-mode selection; recovery rejects rows from another window. Previously admitted cached success must be revalidated and recorded for the current window before it counts.

Logical case execution identity binds test semantics and case selection independent of batching. Every accepted attempt additionally requires `transport_execution_digest`, binding the full actual argv/environment/fixture/config, including grouped or isolated selection switches. The parent validates that selection against the expected logical case mapping; dropping selection switches from all evidence is forbidden.


## Admission inventory migration

`managed-tasks` and `managed-tasks-verify` use a canonical BuildRun manifest plus its SHA256 and a separately pinned resource policy. Task order must be topological; IDs and writable cache keys are unique. The existing capacity, worker transport, tree-reap and output validators remain authoritative. V2 reservation journals bind the task count and ordered full task identities. The old two-independent-phase manifest retains V1 journal bytes and its existing phase paths. V2 uses task IDs for paths so two backend tasks in the same phase cannot collide.

A pending prerequisite yields DEPENDENCY_WAIT. An ordinary failed prerequisite blocks only its descendants, with durable DEPENDENCY_BLOCKED rows; unrelated tasks remain eligible. A REAPED marker alone cannot enable children: the original producer, source inputs, links, task result, output hashes and exact process-tree proof are revalidated. This stage ledger is distinct from release qualification.

The initial bootstrap epoch is intended to contain both Phase2 hello checks, each backend's proper Phase3 build, its three subsystem test binaries (six across both backends), and early Phase4 diagnostic work. Actual produced Phase3 digests cannot be guessed in that epoch. Proper Phase4 requires a subsequent immutable expansion bound to the predecessor epoch, actual Phase3 artifact and hello evidence. Phase4 test work must bind its own produced artifacts rather than borrow Phase2 coverage. Expansion publication and default manifest generation are still pending implementation; the current N-task entrypoint alone does not complete bootstrap orchestration.

Verification status: new native contract/DAG regressions are written but unrun. No process-overlap, crash-injection, full bootstrap or database recovery qualification is claimed by the extraction checkpoints.

<!-- antigravity-early-defect-detection-2026-11-18 -->

## Shared Analysis Tasks, Single-Flight Waiters, and Negative Witnesses (`WP-06`)

Extended by [early_defect_detection_2026-11-18.md](../03_plan/compiler/early_defect_detection_2026-11-18.md) (`ED-05`, `ED-06`, `ED-07`, `ED-T09..ED-T12`, `ED-T24`, `ED-T25`) across `src/lib/common/task_runner/contracts.spl`, `src/lib/common/task_runner/analysis_single_flight.spl`, `src/lib/common/task_runner/scheduler.spl`, `src/lib/common/task_runner/__init__.spl`, `src/app/buildrunner/task_context.spl`, and `src/app/buildrunner/runner.spl`:

### Three-Identity Separation (`snapshot_id` vs `AnalysisKeyV1` vs `lease_generation`)

Analysis scheduling keeps three identities strictly distinct so cache reuse, client coordinate mapping, and retry fencing do not conflate:

| Identity | Owner / Type | Bound Inputs and Role |
|----------|--------------|-----------------------|
| `snapshot_id` | `BuildRunner` / overlay context (`task_context.spl`) | Identifies the client's workspace, worktree, or unsaved editor overlay view used to map spans and authorize fix application |
| `analysis_key` (`AnalysisKeyV1`) | `std.common.task_runner.contracts` (`contracts.spl:38-73`) | Length-prefixed SHA-256 digest (`SIMPLE-ANALYSIS-KEY-1`) binding `(snapshot_id, scope_id, target_id, policy_digest, analyzer_profile)` for single-flight deduplication and admitted diagnostic batch reuse while keeping `lease_generation` and owner/attempt nonces strictly outside `analysis_key` |
| `lease_generation` | `AnalysisJobLeaseV1` / `TaskRunnerAttemptV1` / `compiler_artifact_service` | Monotonic per-attempt execution lease (paired with `owner_id` / attempt nonces outside `analysis_key`) fencing a single worker instance so retries or timed-out predecessors cannot overwrite or poison current state |

### `"analysis"` Task Kind and Parent Output Admission

Supplemental full-lint and explicit LSP/MCP diagnostic runs register under the `"analysis"` task kind on `std.common.task_runner.scheduler` and `BuildRunner`:

- Shares the runner's measured-memory, CPU, and process-supervision budgets while prioritizing interactive/compiler work over background deep lint.
- Enforces the same parent output admission as build artifacts (`ED-T24`): zero exit code is insufficient without current `lease_generation`, reaped worker closure, and verified digests for both the `DiagnosticBatchV1` payload and its coverage receipt sidecar.

### Single-Flight Waiter Attach/Detach (`analysis_single_flight.spl`)

Identical compatible `AnalysisKeyV1` requests from CLI, LSP, and MCP coordinate through `src/lib/common/task_runner/analysis_single_flight.spl` (`ED-T09..ED-T11`):

1. The first admitted request claims producer execution under the authoritative lease; concurrent compatible requests attach lightweight waiter handles without holding a lock during analysis.
2. When an LSP or MCP client cancels or disconnects, `analysis_single_flight` detaches **only that waiter** (`ED-T10`). The underlying producer is **never killed** while at least one other authorized waiter remains attached.
3. Underlying producer cancellation triggers only when the active waiter count drops to zero.
4. Producer crash, timeout, or lease retirement resolves every attached waiter with an explicit terminal `incomplete` / `failed` / `timed_out` receipt, and stale-generation completions are rejected before publication (`ED-T11`).

### `NegativeDependencyWitnessV1` Absence Revalidation

Failed symbol/import/library lookups are cached only alongside a complete `NegativeDependencyWitnessV1` (`src/lib/common/task_runner/contracts.spl`, `ED-T12`) recording the exact scope in which absence was proven:

- Provider-set surface generation and exported-symbol membership.
- Import resolution and library search-path order.
- Watched directory or generated-file inventory digest.
- Candidate overload/implementation set and active target/feature flags.

Before reusing any cached negative finding, the runner revalidates every witness against the current snapshot; adding a formerly missing file, export, overload, or optional library invalidates the witness immediately. Unfinished or unscheduled providers remain `Pending` / `Unavailable` and never emit a `NegativeDependencyWitnessV1`.
