# Container retention/subject follow-ups from the #9722 review (2026-11-16)

Status: open

Source: the independent review of assembly unit E (PR #9722, merge
`52bc1164218`), receipt
`.spipe/simple_orchestrator/continuation_20261116/milestone_0012_assembly/review_groupE_retention_probes_stats_r1.sdn`.
All five are P2. Each one fails closed: no capacity or custody is released
silently. Execution: NOT_RUN. These are source-trace findings only.

## 1. A native-retired subject goes back to cleanup on any error

`subject_workspace_current_v3` (`src/lib/nogc_sync_mut/io/linux_fresh_workload_subject_v2.spl:549-556`)
moves every phase that is not closed to `cleanup` when an error occurs. That
includes the irreversible `native-retired` phase. Any later
`validate_workspace_containment_v3` call that fails invalidates the retirement
token, because `subject_native_retirement_current_v3` requires `native-retired`.
This contradicts the comment at `:626`.

Fix: only transition when `phase == "ready"`, which is what `subject_stats_v1` already does.

## 2. A shared bindings index lets one subject type poison the other

CPU subjects and workspace subjects share one bindings index, keyed by
containment binding digest (`nogc_sync_mut/io/linux_fresh_workload_subject_v2.spl:258-262,551`, `linux_fresh_workload_native_v2.spl:191`).
A call with the wrong subject type returns `request-changed`, and the wrapper
then moves the other path's live subject to `cleanup`.

Fix: return the type mismatch before the cleanup transition, or check
`workspace.is_some()` in `native_v2` before making the call.

## 3. A stats parse failure tears down a live subject

Any stats read failure moves the subject to `cleanup`, even though the read
does not change anything (`subject_v2.spl:524-530`,
`common/contracts/container/linux_cgroup_stats_v1.spl:100-104`). A parse
failure counts. With `blkcg_debug_stats`, `io.stat` can carry `depth=max`,
which fails the digit check. So one telemetry read ends the workload.

Fix: keep the cleanup transition for custody and identity failures only. For
parse errors, return the error without changing the phase. Also tolerate
non-numeric `io.stat` keys that the parser does not consume.

## 4. Attach is allowed without a completed primary observation

The attach gate `subject_primary_effect_v3` checks quarantine, confirmed,
ready, key and Inspect. It does not check `primary_observed`. As a result,
stdin-enabled attach is offered even when there is no exact-executable proof,
or when the last proof failed. The #9716 design leaves this check to the upper
layer, so the gap is defense in depth only.

Fix: require `state.primary_observed` on the attach path only.

## 5. `close_v1` has no authorized cleanup after an agent effect

In `nogc_async_mut/container/providers/linux/workspace_mount_owner_v1.spl:394-409`, once `agent_effect_attempted` is set,
`close_v1` refuses every time, and nothing provides an authorized cleanup
path. The slot keeps its exclusion, root and parent FDs, plus one of the 32
`workspace_source_active_v1` slots, until the process exits. After 32 staging
attempts, including failed ones, the source owner is exhausted.

Fix: name the owner of authorized cleanup and implement it there, or record
the bound as a deliberate limit with a test that pins it.
