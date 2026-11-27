# Container fresh route: no `wait` or `logs` read through the shared API

- **Status:** OPEN (2026-11-27)
- **Component:** Simple Container shared API, Linux Podman fresh install route
  (`src/lib/nogc_async_mut/container/providers/linux/fresh_epoch_workload_v2.spl`,
  `src/lib/common/contracts/container/linux_fresh_workload_v2.spl`,
  `src/lib/common/contracts/container/linux_fresh_workload_inspect_v2.spl`)
- **Found:** 2026-11-27, by reading the route while fixing
  `container_fresh_route_workspace_tty_unsupported_2026-11-27.md`. Not observed
  live: this host has no installed machine policy.
- **Spec cases affected:** every case of
  `test/03_system/app/container/feature/podman_shared_api_live_spec.spl` that
  calls `live_run_v1` (workspace, limits, stdout/exit code, TTY, cleanup) —
  5 of 6. Only the refusal case does not reach it.

## Symptom (from source)

`live_run_v1` runs `prepare`, `create`, `start`, then
`simple_container_read_v2(owner, "wait", ...)` and `"logs"`.

`simple_container_read_v2` accepts both actions and forwards to
`LinuxSimpleContainerAdapterV2.read`, whose fresh branch calls
`LinuxFreshWorkloadOwnerV2.read_v2`. That method answers only `inspect`,
`configuration` and `input-configuration`:

```
linux-fresh-workload-read-action-unsupported:wait
linux-fresh-workload-read-action-unsupported:logs
```

So the workload's exit code and stdout are unreachable on the fresh route.

## Why it is not a small read

- `LinuxFreshWorkloadActionV2` is a closed enum with no wait or logs action,
  and `machine_fresh_workload_action_initial_v2` has a closed action-name list
  with a reserved history budget per workload.
- The fixed 42-field V2 inspect schema has no exit-code field. The workspace
  lane's V3 schema does (`exit_code`, `tty`, `open_stdin`), so the shape exists
  but is not reachable from a CPU V2 record.
- A logs read needs a bounded-output closed action through the installed
  launch owner (`podman logs` is not in the V2 argv projection).

## Options

1. Add closed `Wait`/`Logs` actions to the fresh V2 route: an inspect that
   includes `State.ExitCode`, and a bounded `logs` projection, each with its own
   history budget and settlement rule.
2. Route the live spec's read side through the lane that already has exit-code
   observation (workspace V3 primary), which needs the lent-workspace owner.

Owner decision; not taken here.

## Acceptance

`live_run_v1` returns the workload exit code and stdout on the fresh route in
the guest VM, and the five affected cases pass without changing the cases.
