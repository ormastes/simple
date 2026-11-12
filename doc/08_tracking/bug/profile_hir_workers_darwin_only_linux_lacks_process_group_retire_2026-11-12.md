# Profile HIR workers have been Darwin-only since 35541505cd5: Linux lacks PROCESS_GROUP_RETIRE

- Status: fix-implemented (verification pending a runtime-authority + Stage 2 rebuild)
- Severity: P1. On Linux, every HIR shard pool (the coordinator and the Stage 3 capsule) runs serially.
- Found: 2026-11-12, by the early Phase 3 lane on aarch64 Linux
- Component: `src/runtime/runtime_process_owned.c` (Process Observation V4 owner)

## Observation
With every env admission fixed (#8610, #8619, #8639), the HIR profile admits the pool, but every owner fails to start:

```
[hir-shard] owner=0/2@0 reason: HIR worker process observation unavailable: process-group-retire
```

`worker_hir_owner_start_v1` requires the full monitor-group capability set (`process_observation_monitor_group_gap_v4`) and asks for the `ProcessGroup` descendant policy. On Linux the C owner:
- never advertised `POV4_CAP_PROCESS_GROUP_RETIRE` (`POV4_CAPABILITIES` has it only in the Darwin set);
- admitted only `POV4_DESCENDANT_LEADER` outside Darwin;
- had no Linux body in `owned_group_retire_ready`: it fell through to `#else return 0`, so a Linux group could never retire.

## Why runs 13 and 15 did not show it
- Their phase C matrix tool rows resolved to `[shard] threads=1`, because the host bound was 2 and the 24 GiB parse estimate applied. So no HIR pool was ever spawned.
- The Stage 3 capsule HIR pass was refused earlier, before any owner start, because its `native-build ...` base failed the canonical-route check (fixed in #8520). After that, absent-turned-empty env keys refused it (fixed in #8610, #8619 and #8639).
- The failure only became visible after #8639 added the `reason:` print. Until then a failed start showed only `status=CRASH exit=-1 claimed=0`.

## Fix (this change)
- `owned_linux_group_live`: counts the live members of a pgid with a `/proc` scan. It splits each `/proc/<pid>/stat` at the LAST `)`, because comm may contain spaces or parentheses. A member counts as live unless its state is `Z`/`X`. A process that exits mid-scan (ENOENT/ESRCH) counts as absent. Any other read or parse failure is a sampling failure and never counts as absence.
- `owned_group_retire_ready` now has a Linux body, the same one Darwin uses, with this order: deadline check, then scan, then signal only a group the scan found non-empty. The unreaped leader pins pgid == pid, so the id cannot be recycled between the scan and `kill(-pgid)`. The check runs only for an exited, unreaped leader (the retire check) and at the cleanup deadline, never on an ordinary poll tick.
- Fail closed: `POV4_CAP_PROCESS_GROUP_RETIRE` is advertised, and `POV4_DESCENDANT_PROCESS_GROUP` is admitted, on Linux only when a probe scan of this process's own group succeeds (`owned_linux_group_retire_available`). Otherwise the owner refuses exactly as before.
- No new exported `rt_*` symbol.

## Alternative considered (for review)
`prctl(PR_SET_CHILD_SUBREAPER)` on the coordinator, plus `waitid(P_PGID, pgid, WEXITED|WNOHANG|WNOWAIT)`. This would avoid the `/proc` scan, and orphaned group members would be reparented to the coordinator, so it could observe them. However:
- it changes reparenting for every descendant of the coordinator process, not only HIR workers, and makes the coordinator responsible for reaping all of them;
- `waitid(P_PGID)` reports exited members, not running ones. A count of live members still needs bookkeeping, or a second probe such as `kill(-pgid, 0)`, and that probe cannot tell zombies from runners;
- it does not cover members that never became the coordinator's descendants.
The `/proc` scan is local to the owner, side-effect free, and matches the Darwin semantics (a zombie is not live).

## Evidence
- `src/runtime/test/runtime_process_group_retire_linux_selfcheck.c`. The test runs a leader in its own pgid together with a grandchild, then lets the leader exit unreaped. It asserts four things: the capability is advertised; "not ready" holds while the grandchild runs; "ready" is reached only after the grandchild is retired; and ready comes from an empty-group sample, not the cleanup deadline.
  - Red on origin/release/1.0.0 `196100d40ec`: 3 failures (capability not advertised, never ready, grandchild still running).
  - Green: 8/8 checks, stable across 4 consecutive runs.
- `check-c-runtime-compiles-push.shs`: the same 20 pre-existing vector-provider failures on base and on this change. `runtime_process_owned.c` compiles clean with `-Wall -Wextra`.
- Native confirmation is PENDING: a Phase 1 runtime authority plus Stage 2 rebuild, then the 3-file pre-flight (`completed_workers=2`) and the Stage 3-shape probe. This is sequenced by the coordinator around run 17.
