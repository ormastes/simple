# V4 agent records every self-exited agent as failed

Status: CLOSED (source fix). The fix is in the same change as this record
(milestone_0034, owner decision N7). The specs are authored but NOT_RUN,
because this host has no runnable `simple` binary, so runtime verification is
still pending.

## Defect

`host_linux_service_agent_v4.spl` (inspect stage, about line 902 at
`b1a3b9318cf`) classified a workload that left `running` with this test:

```
if operation.state.exit_code == 0: "succeeded" else: "failed"
```

That value comes from `machine_fresh_workspace_workflow_v3.spl:27`, which builds
every V3 reply with `RuntimeStateV1(phase, identity, -1, ...)`. V3 never observed
the workload's exit:

- Inspect and Stop reported only cgroup population (`:122-128`).
- The fixed Podman inspect projection had no `ExitCode` field
  (`linux_fresh_workload_inspect_v2.spl:9-12`, and therefore also
  `linux_fresh_workspace_inspect_v3.spl:10-12`).

So `exit_code == 0` was never true, and every self-exited agent, including
those that exited 0, was settled with outcome `failed`.

## Fix

The library now observes the exit status natively:

- `linux_fresh_workspace_inspect_format_v3` gains
  `"exit_code":{{json .State.ExitCode}}` (47 fields).
- `linux_fresh_workspace_exit_status_v3` decodes the read into a typed
  `RuntimeExitStatusV1`:
  - `Exited(code)` only when the status is `exited` or `stopped`, `pid` is 0
    and the code is in 0..255.
  - Any other status becomes `NotExited(status)`.
  - An engine failure or a field that cannot be decoded becomes
    `Unknown(reason)`.
  - Nothing defaults to 0.
- The V3 `Stop` and `Destroy` workflows begin with a single-use `inspect-exit`
  stage. It runs before the engine stop, because after a stop `ExitCode` is the
  stop signal rather than the workload's own exit. Destroy reuses an earlier
  completed read.
- The read is skipped once any `stop` exists, because the code would then be
  the stop signal.
- Every V3 reply now carries the status in `RuntimeStateV1.workload_exit`, which
  defaults to `Unobserved`. A read the engine fails, or one that cannot be
  decoded, is kept as `Unknown` and does not latch the lifecycle. A helper
  timeout or a spawn failure still latches, like any other effect.

The agent change:

- When the workload's own exit is the first stop cause, the agent sets
  `exit_by_workload` and holds the outcome at `failed`.
- `host_agent_destroy_exit_v4` then settles the outcome from the Destroy reply.
  Only `Exited(0)` is `succeeded`. `Unobserved`, `NotExited`, `Unknown` and
  non-zero exits all stay `failed`, so the agent fails closed.
- A cancel or window-end first cause keeps its own outcome.
- The exit and destroy digests bind the typed status (`workloadExit`).

## Specs (NOT_RUN)

- `test/01_unit/lib/orchestration/host_linux_service_agent_v4_exit_outcome_spec.spl`
- `test/01_unit/lib/container/linux_fresh_workspace_v3_spec.spl`, in the
  "Engine-native workspace exit status v3 (N7)" group.
