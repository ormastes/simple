# Native V4 ProcessGroup: Stage 6A blocker

Status: BLOCKED; investigation only. No runtime capability, request policy, or
receipt evidence was changed. Baseline: origin/main `fdc600a4d3f`.

## Observed implementation

- `src/runtime/runtime_process_owned.c`, `POV4_CAPABILITIES` and
  `rt_process_observation_v4_start_pinned_value` admission: only LeaderOnly is
  supported; ProcessGroup is rejected with ENOTSUP/provider failure.
- `pov4_signal_owned_child`: signals the pidfd or positive leader PID. This
  cannot retire a group whose leader exits before its descendants.
- Shared owned async polling observes exit with `waitid(...WNOWAIT)` and then
  immediately calls `wait4`. `pov4_reconcile_gone_child_locked` also consumes
  the child through `waitpid`. A group implementation must audit both paths,
  startup cleanup, cancellation, and unpublished-ticket cleanup: early reap
  releases the leader PID reservation before later group signals.
- `pov4_snapshot` explicitly emits `tree_empty=0` and `tree_empty_ns=-1`.
  Existing v2 group cleanup sends SIGKILL before reap; successful signal
  delivery alone is not proof that every group member has retired.
- Bounded stream retention and fair per-stream drain quanta already exist in
  the shared owner. EOF alone cannot prove retirement: a live descendant can
  close both capture descriptors. Conversely, exited leader does not imply
  EOF because descendants may retain those descriptors.
- `src/runtime/simple_core/core_process_observation.spl` is an older
  observation provider with explicit unavailable serialization, identity-safe
  cleanup, compiler ABI, and bounded-hash prerequisites. It is not a usable
  pure-Simple V4 twin for a new C lifecycle implementation.
- `src/lib/common/process/observation_v4.spl` validates tree evidence and
  cleanup receipts separately. Cleanup receipt validation currently rejects
  tree-control/tree-empty claims; successful-path edits alone are insufficient.

## Required owner transitions

1. Admit ProcessGroup only when the provider can reserve the leader identity,
   establish the group before exec, and supply a bounded retirement mechanism.
   Preserve executable/cwd pin and binding checks and the single deadlines.
2. Running -> leader-exited-but-unreaped: observe with WNOWAIT; preserve exact
   child ownership. Record exit observation separately from final waited time.
3. TERM -> KILL: target the owned group while its identity reservation remains
   valid, even after leader exit. Distinguish attempted, delivered, absent,
   permission failure, and identity loss. ESRCH reconciliation must not consume
   the leader until group cleanup is settled.
4. Retirement-pending: retain bounded capture/draining and cleanup ownership.
   Prove the owned group has no remaining live members using an admitted
   identity-safe mechanism; account explicitly for the retained zombie leader.
   Do not use kill success, pipe EOF, or a racing unbounded process scan as proof.
5. Proven-retired -> exact leader reap -> frozen receipt -> matching ACK.
   Emit tree-empty time and validity only from the retirement observation.
   Cleanup timeout or unverifiable membership must preserve a failure/cleanup
   receipt and must not become a successful frozen execution receipt.

The provider design must state whether members that call setsid/setpgid are
outside its contract. If Stage 6A requires all descendants including escaped
members, a process group alone is insufficient; require stronger containment.
Do not change the requested descendant policy to LeaderOnly.

## Acceptance checks before capability admission

- Leader exits first; descendant retains pipes and ignores TERM: group KILL
  retires it before successful collection, and leader remains unreaped until
  retirement proof is complete.
- Descendant closes both pipes but continues running: EOF does not permit
  success. Cover quiet descendants, natural exit, cancellation, and deadline.
- Concurrent unrelated group remains alive through TERM/KILL; stale tickets
  cannot signal it. Inject identity loss, ESRCH, EINTR, and wait failures.
- Continuous stdout/stderr exceed capture limits: bounded retained memory,
  fair drain progress, accurate byte/truncation counters, bounded cleanup.
- Startup failure after fork, unpublished ticket failure, frozen replay,
  mismatched ACK, and valid ACK preserve ownership and exactly-once cleanup.
- Validate native provider and pure-Simple twin with the same fixtures; refresh
  V4 receipt decoder checks, runtime selfchecks, integration SPipe/manuals, and
  Stage 6A real pinned CLI evidence. These are required checks, not executed
  or claimed passes in this report.

## Session evidence and limits

Read-only inspection of the named source owners and existing V4 tests; no
native execution, compilation, or acceptance check was run. A full worktree
checkout failed and cleaned itself up. A sparse worktree containing relevant
runtime/contracts/tests occupies approximately 9.6 MiB. The host had only
2.3 GiB free, so no build cache or shared worktree was deleted or created.
Implementation remains blocked on the retirement mechanism and pure-Simple
owner design above; this report does not claim Stage 6A completion.
