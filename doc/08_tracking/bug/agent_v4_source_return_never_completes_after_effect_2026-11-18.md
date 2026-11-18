# Agent V4 source-return never completes after a staging effect

- Date: 2026-11-18
- Status: PARTIAL. Source-return is fixed (pending land). Final close is still blocked (see "Remaining block").
- Severity: high. Every V4 agent run wedged before Host settle, and the charge never settled.
- Found at: `2cf8e62e41f` (milestone_0030 L10), verified by an opus reviewer.
- Design precedent: `doc/05_design/agent_workspace_retention_v3.md`

## Chain

1. `src/lib/nogc_sync_mut/orchestration/host_linux_service_agent_v4.spl:943-947`: stage `source-return`
   calls `simple_container_return_settled_workspace_source_v3`. On error it keeps the stage and retries.
2. `src/lib/nogc_sync_mut/container/machine_authority_v1.spl:989`: `return_settled_workspace_source_v3`
   calls `machine_workspace_source_return_settled_v3`.
3. `src/lib/nogc_sync_mut/container/machine_fresh_workspace_source_transition_v3.spl:86` calls custody `cleanup_v3`.
4. `src/lib/nogc_sync_mut/container/machine_fresh_workspace_source_custody_v3.spl:84` calls
   `LinuxWorkspaceSourceOwnerV1.close_v1`.
5. `src/lib/nogc_async_mut/container/providers/linux/workspace_mount_owner_v1.spl:405-408` refuses with
   `agent-workspace-retention-requires-authorized-cleanup`, because staging always sets
   `agent_effect_attempted` (`:286`).

Every agent run that reaches `source-return` has staged, so the refusal is unconditional. Stage 1
retries forever and Host settle never runs. `retire_native_v3` (`workspace_mount_owner_v1.spl:367`)
is the operation the retention design names for this point, and it had no caller.

## Fix (retained return, per the retention doc)

- **Stage `settle`.**
  - `machine_authority_v1.settle_workspace_v3` keeps its `epoch_current_v3` fence and calls
    `machine_workspace_settle_v3`.
  - With a staging effect, that function runs `machine_workspace_settle_retained_v3`. In order, it:
    1. re-proves absence;
    2. checks primary transport and probe capture;
    3. mints the native token from the original epoch custody, only once;
    4. has the source re-prove absence and commit `native-retired-retained`
       (`custody.return_retained_v3`, using the custody's own full invocation);
    5. builds the retention row (`machine-workspace-retained-returns-v3`, canonical retained metadata);
    6. reserves the settlement;
    7. publishes settlement and retention in ONE `workload_publish_v3` batch.

    No crash window can leave storage charged without a retention row.
  - Other workspaces keep the unchanged `machine_fresh_workload_settle_workspace_v3`.
- **Retryable publication.**
  - A settle batch whose commit outcome is unknown (`uncertain` with permit `settlement-reserved`) is
    resolved by store readback before any new effect.
  - If the store head equals the history head, nothing was committed. The reservation is released
    (`settlement_publication_abandoned_v3`) and the batch is rebuilt. The native token is NOT re-minted.
  - If the head's parent is our head and the head contains our retention row key, the exact store
    segment is adopted, replayed and verified.
  - Anything else refuses fail-closed (`machine-fresh-workspace-settlement-publication-foreign`).
- **Stage `source-return`.**
  - `return_settled_workspace_source_v3` is now epoch-fenced (`epoch_current_v3`).
  - With a staging effect it calls `machine_workspace_source_return_retained_v3`, which has no effect,
    publication or close. It only moves the lifecycle source phase to `retained-returned`, a name
    distinct from the pre-reserve `retained`.
- **Unchanged.** Generic `close_v1` still refuses. Custody `cleanup_v3` refuses both retention phases
  instead of re-entering `close_v1`. The storage lease is never released. Host V4 is unchanged.
- **Failed staging (`retained-failed`) cannot reach settle.**
  - `begin_binding_v3` refuses unless the stage phase is `staged`.
  - A workspace record is reserved only with that binding.
  - `retire_native_v3` also refuses without a staged runtime binding.

## Remaining block (P1, owner decision pending; NOT fixed here)

The final close of a retained workspace always refuses, so neither release nor epoch close runs:

- `src/lib/nogc_sync_mut/container/machine_fresh_workload_lifecycle_v2.spl:863`
  (`close_native_v2`): `if not ["none", "returned"].contains(state.source_phase): return
  Err("machine-fresh-workspace-source-parent-retained")`. The source phase is now `retained-returned`.
- `src/lib/nogc_sync_mut/container/machine_authority_v1.spl:1005-1009` (`close_workload_v3`) reaches
  `self.state.close_native_v2()?` and fails there.
- `src/lib/nogc_sync_mut/orchestration/host_linux_service_agent_v4.spl:1874`, the agent's step-3
  workload close, returns that error. As a result, `host_linux_service_agent_release_v4` (`:1890`)
  never sets `workload_closed`, and `simple_container_close_epoch_v3` (`:1921`) never runs.

This is not a regression. Before the fix the agent never got past `source-return`. Who may clean up
or recover a retained root, and whether close may hand it to a durable owner, is retention policy
that the doc leaves to the owner.

## Specs (AUTHORED_NOT_RUN: no runnable binary)

- Reproduction:
  `test/01_unit/lib/container/agent_source_return_v3/agent_source_return_retained_v3_spec.spl`
- Generalization: generic close refuses, cleanup refuses a retained source, lifecycle close still
  refuses, failed staging cannot reach settle, and no caller-facing surface reaches the path.
  `test/01_unit/lib/container/agent_source_return_v3/agent_source_return_refusals_v3_spec.spl`
- Behavioural native consumers (NOT_RUN):
  - `check_effect_source_return_completes_v3` in
    `test/fixtures/agent_workspace_retention_v3/source_return_scenarios.spl` drives settle, then a
    first-call source-return that completes, then the named refusal on a stray retry.
  - `check_retained_return_keeps_written_root_v3` in
    `test/fixtures/agent_workspace_retention_v3/scenarios.spl`.
- No runtime-free behavioural path exists. The transfer, quota slot, fresh-epoch subject and machine
  store are native owners with no DATA constructor, so the unit specs are structural pins.

## Open gaps (doc silent; smallest fail-closed choice)

1. **Foreign store head.** If another commit landed after our batch, resolve refuses fail-closed
   instead of searching deeper history.
2. **Outcome vocabulary.** `host_linux_completion_evidence_v3.spl:127` requires
   `source_return == "returned"`. No `retained` outcome value was added, because that would be a codec
   change.
3. **Build arm.** A remote-build arm (lane A) routed here refuses at `retire_native_v3` until it has a
   build analogue.
