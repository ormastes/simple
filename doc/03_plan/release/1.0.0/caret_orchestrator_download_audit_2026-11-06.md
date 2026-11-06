# Caret orchestrator Downloads plan — initial release audit

Date: 2026-11-06. Status: **SOURCE AUDIT ONLY; implementation incomplete; runtime qualification NOT_RUN**.

Input: `/Users/ormastes/Downloads/simple_caret_orchestrator_shared_daemon_full_plan_2026-11-06.md` (113,358 bytes, revision1.0). Its inspected baseline is `3ef23d69caa361369603a761f114c5613f7ea7b7`. This bounded audit inspected the release-next worktree and its new checkpoint `a324376253be34e74bac31bf1aecc27fa9a59183`; initial comparisons used its preceding `6a4a4bee184a68864fc2510f6ea2023bedb9f4cc` HEAD plus current source. It does not certify every requirement, transitive caller or platform. Only this audit file was changed for this task. Root owns the byte-identical input archive and PR.

“Existing” below means concrete source/consumer found. “Partial” means reusable source exists but the requested end-to-end contract is incomplete. “Missing” means the proposed integration was not found in the inspected paths, not a proof of repository-wide absence. No historical summary, design claim or authored spec was promoted to a runtime PASS.

## Existing, partial and missing

| Plan scope | Current evidence and remaining gap |
| --- | --- |
| CFG-01/02 — partial | `src/lib/common/contracts/orchestration/{resource_v1,ci_v1}.spl` provide strict Pod/Deployment and Job/Pipeline decoding, with existing fixtures. The ResourceList/profile/AgentSession/HostPool dispatch, immutable authorized plan and schema-derived tooling are not established by these decoders. ResourceV1 still explicitly limits its scope to Pod/Deployment. |
| DAE-01/02 — concrete unsafe paths remain | `src/lib/nogc_sync_mut/daemon_sdk/daemon.spl:64` calls the handler, ignores response-write success, then marks the request for clearing. `client.spl:42` can kill the recorded PID after failed responsiveness. New Caret owned leases do not migrate these SDK callers automatically. |
| DAE-03/05 — partial | `src/lib/common/task_runner/distributed_operation_journal_v2.spl` already owns immutable operations, transitions and executing-to-outcome-unknown recovery. Its header explicitly excludes power-loss fsync and bounds history at100,000 events. Durable checkpoint/compaction and retained dedupe horizons are not demonstrated. Preserve the independent build/test journal and its domain authority. |
| DAE-04/RUN-01 — partial | SDK dispatch is serial; max_concurrent bounds a loop, not simultaneous effects. Test CLI still selects light_daemon, separate from generic SDK composition. Light daemon has newer wakeup-sequence optimization, so the old plan understates that improvement; it remains a serial domain path, not the proposed asynchronous shared host service. |
| HOST-01/02/03 and ORCH-01/02/03 — missing integrated service | Container capability and distributed-authority contracts exist. No complete enrolled host/controller, machine-wide hard reservation ledger, fenced prepare/commit execution handshake or resource-profile placement service was found in the scoped app/contracts search. Fiber scheduler progress overcommit must not become host quota admission. |
| CTR-01/02 — partial | Linux OCI lifecycle is genuinely called by `src/app/ci/pipeline_runner.spl:302` onward; preserve it. Linux provider now includes additional exact logs/bounded state work, but stats still returns explicit unavailable. Interactive workspace/env/secret/TTY/device conformance is not established. Legacy `test_runner_container.spl:160` still invokes global volume prune; test-daemon container adapter still uses shell/name-based removal. |
| CTR-03 — newer partial source, conflicting engine choice | `providers/windows/hcs_runtime_v1.spl` now exists, unlike the older proposed-only baseline. It explicitly selects containerd+runhcs, includes scripted/fail-closed paths, and is not the requested Docker process provider or proof of the specified Windows host/image qualification. Reconcile the architecture decision before replacing/expanding this owner. |
| MUX-01/02 — partial | CoreMux contracts, owner, client, leases and action separation exist. Inspected smux server dispatch still routes the legacy protocol; client configuration remains literal IPv4 loopback. The wire design explicitly records28 authored NOT_RUN cases and unfinished production/Caret integration. No authenticated bind-existing-runtime operation or complete terminal ownership migration was established. |
| CARET-01/02 — partial | Native session binding/control and pane/workspace routes exist. `agent_plan.spl:56` still uses Codex argv or a Claude-style fallback, not independently qualified provider adapters. No complete SDN-template-to-placement-to-CoreMux session flow was found. Messaging AgentSessionRegistry is a different domain, not the proposed orchestration AgentSession resource. |
| RUN-02 — guard exists; remote path missing | `src/app/buildrunner/database_session.spl:34` rejects remote process evidence. Keep this rejection until parent-verified input/toolchain/attempt/output acceptance exists; deleting it would regress safety. |
| OPS-01/EXT-01 — partial/missing qualification | Domain diagnostics and contracts exist, but the complete resource-to-runtime-to-terminal correlation/operational service is not established. FreeBSD jail and macOS native-sandbox leaves now exist; neither establishes Apple Linux-VM or Kubernetes adapters. Native macOS helper comments explicitly state the required authenticated helper is absent. No platform PASS is inferred. |

## Relationship to the saved memory/source work

The new Caret source-session authority, HTTP worker and owned-agent lease path are **authored local foundations**, with real consuming source routes and required native-child/concurrency specs. They improve exact process ownership, scoped logical sessions, bounded cleanup and identity handling. They do not implement host enrollment, distributed resource scheduling, container terminal attachment, a durable shared daemon or remote evidence acceptance. Ordinary stdio remains unbound to that HTTP authority.

Similarly, compiler ownership hardening and source diagnostics/structural views support safer implementation and inspection; they do not satisfy the plan's host resource ledger or distributed operation proofs. Preserve these lanes and their unexecuted acceptance gates instead of duplicating their owners.

## Prerequisites and next slice

1. Finish admitted self-hosted runtime/bootstrap qualification and execute the saved memory/source/owned-process gates. No seed fallback, no inferred PASS from authored specs.
2. Record exact local daemon entrypoints, journal ownership and existing client behavior before migration. Reuse owned service/group-process mechanisms and distributed-operation V2; keep build/test V1 semantics.
3. **Recommended candidate, not selected:** a local-only DAE-01/DAE-02 safety slice. Compose one existing SDK consumer with exact-instance recovery and journal-backed immutable request outcomes, atomic response publication and acknowledgement. Retaining a request alone is insufficient: redelivery must not rerun an already-performed effect.
4. Exit gates: injected response failure preserves recoverable outcome without duplicate effect; same ID/different payload rejects; crash around intent/effect/outcome preserves uncertainty; stale PID/owner cannot kill another process; legacy local request behavior remains compatible. No host enrollment, remote launch or platform expansion belongs in this slice.

## Requirement choices still needed before expansion

The imported plan records Podman-first and a Docker-first Windows preference; preserve that intent, but do not treat it as runtime qualification or permission to replace installed environments. The following remain explicit planning choices, not selected by this audit:

| Choice | Benefit | Cost/risk | Indicative effort |
| --- | --- | --- | --- |
| Local shared-daemon safety slice first | Reuses current ownership work and removes concrete hazards | Does not yet deliver distributed Caret UI | 1–2 focused person-weeks after runtime admission; estimate only |
| Full native Podman host/Caret vertical slice | Exercises the intended user workflow | Requires Linux fixture, secure transport, ledger, stream ownership and much wider regression scope | Several person-weeks; use plan's package ranges, not a delivery promise |

Before the broader slice, select designated host/image/engine fixtures, native versus existing Kubernetes placement authority, journal durability/retention profile, allowed GPU-sharing policy and numerical performance budgets. Process-crash versus power-loss durability, optional platform scope and the recorded Windows11 machine must remain visible decisions. No new requirement option is auto-selected here.

The full plan's definition of done is **not met**. This audit supports saving the current release work and choosing a bounded continuation; it is not release verification or authorization to mark the unfinished PR ready.
