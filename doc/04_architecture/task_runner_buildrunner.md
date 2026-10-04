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
