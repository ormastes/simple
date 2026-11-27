# Container fresh route: no `wait` or `logs` read through the shared API

- **Status:** FIXED IN SOURCE (2026-11-27), unit-proven for the pure parts only;
  the stateful path and the live guest run are unverified (see "Fix" below)
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

Decision and fix below (a third route, narrower than option 1).

## Acceptance

`live_run_v1` returns the workload exit code and stdout on the fresh route in
the guest VM, and the five affected cases pass without changing the cases.

## Fix (2026-11-27): named `wait`/`logs` stages over the existing probe projection

Neither option was taken as written. Option 1 would widen the closed
`LinuxFreshWorkloadActionV2` enum and add a `podman logs`/`wait` argv; option 2
needs a different owner. The lower probe lane
(`doc/05_design/linux_fresh_workload_probes_v3_20261116.md`) already has the
closed pieces, so they are reused instead of duplicated:

- `LinuxFreshWorkloadProbeActionV3 { Wait, Logs }` and
  `linux_fresh_workload_probe_project_v3` — rewrites the genuine, successor-bound
  17-argument Inspect launch into the fixed tail `<verb> -- <native id>`. No
  `--follow`, `--latest`, `--tail`, format or container name can be selected.
- `linux_fresh_workload_probe_bind_v3` / `_validate_v3` — bind and re-validate
  that projection against the installed custody.

What is new:

- `wait` and `logs` are two **named stages of the Inspect action** (like
  `inspect-created` / `inspect-exit`), not enum values. The begin path is the
  one existing `machine_fresh_workload_begin_v3`; only the launch bind/validate
  branches (`workload_launch_bind_v3` / `workload_launch_validate_v3`), and the
  post-publish revalidation uses the same projected validator.
- Ordering (`linux_fresh_workload_read_prior_v3`): `wait` needs a completed
  `inspect-confirm` (the confirmed start); `logs` needs a completed `wait`, so
  logs is never a read of a running workload and never follows.
- `LinuxFreshWorkloadOwnerV2.read_v2` answers `wait` and `logs` through
  `observe_v3`. Result shape mirrors the OCI provider's native wait: phase
  `exited`, workload exit in `state.exit_code`, helper exit in `exit_code`,
  raw output in `stdout`.
- The probe custody lane is **not** used: its selection demands a compiled
  provider-CLI request (no TTY, no build roots), accepts only exit `0`, and
  changes `stop`'s prior. A record that has probe custody refuses the plain
  reads (`machine-fresh-workload-read-probe-lane-owned`).

### Bounds

- **Identity:** the native id is the transfer's retained one; the caller
  supplies only its original request (`machine-fresh-workload-request-changed`
  otherwise). CPU V2 records only — a workspace V3 record is refused
  (`machine-fresh-workspace-explicit-v3-port-required`).
- **Deadline:** one helper per read, under the request's own `timeoutMs`
  (<= 30000 ms) both as the helper timeout and the collector deadline.
- **Size:** the existing 65536-byte collector cap
  (`machine-fresh-workload-output-limit`) and the 65536-byte action-row
  evidence cap. Over the cap is a refusal, never a truncation.
- **Once only:** each read runs one helper. A completed read is replayed from
  the retained result; an attempted, unresolved one stays refused
  (`machine-fresh-workload-action-already-attempted`).
- **History:** two commits per read from the non-cleanup budget (limit 44), so
  the Stop/Remove/Absence reserve is untouched.
- **Exit code:** `linux_fresh_workload_wait_exit_code_v3` accepts exactly one
  canonical decimal in 0..255 with at most one line ending.

### Gating decision: no new installed-profile key

`workloadBuildRootPrefix` and `workloadTerminalMode` gate what a *container may
be configured to do* (bind a host path, allocate a TTY). These reads add no
container configuration and no argv the installed profile does not already
permit: the probe lane runs the same `wait`/`logs` projection under the plain
34-key profile. The owner reads only the container it created. So no key was
added, and the two-key "both or neither" profile shape is unchanged.

### Failure latching (read from source)

A read that times out, exceeds the cap, exits non-zero or prints a non-canonical
exit status sets `outcome_unknown` (not `uncertain`). Further non-cleanup
actions are then refused, but `stop`/`remove`/`absence` and settlement still
run (`stop`'s prior becomes `create`), so `destroy` stays reachable. A refusal
before any row (wrong order, changed request) latches nothing.

### Files

- `src/lib/common/contracts/container/linux_fresh_workload_probe_v3.spl` —
  `linux_fresh_workload_read_action_v3`, `_read_prior_v3`,
  `_wait_exit_code_v3`, `_read_command_v3`.
- `src/lib/nogc_sync_mut/container/machine_fresh_workload_record_v2.spl` —
  `wait`, `logs` in the CPU record's closed operation-name list.
- `src/lib/nogc_sync_mut/container/machine_fresh_workload_lifecycle_v2.spl` —
  ordering and the probe-lane exclusion in `action_begin_v2`.
- `src/lib/nogc_sync_mut/container/machine_fresh_workload_effects_v3.spl` —
  bind/validate branch; `wait` output check before completion.
- `src/lib/nogc_sync_mut/container/machine_authority_v1.spl` —
  `read_output_v3`, `read_completed_v3` on the transfer.
- `src/lib/nogc_async_mut/container/providers/linux/fresh_epoch_workload_v2.spl`
  — `observe_v3`, `read_v2`.

### Evidence, and what it does not cover

- `test/01_unit/lib/container/linux_fresh_workload_read_v3_spec.spl` (5 cases)
  and one added case in `machine_fresh_workload_record_v2_spec.spl`: read names,
  ordering, exit-code parser, read command identity, fixed projected tail.
- **Not executed by any test here:** the lifecycle, effects, authority and
  owner changes need a real installed custody. They were checked only by the
  specs that import those modules still loading and passing.

## Still open after this fix

1. **Live run unverified.** Acceptance is in the guest VM; not run.
2. **Fast-exit workloads may fail at `start`, before `wait`** (from source, not
   observed): `perform_v2("start")` runs Start, Inspect and association and
   refuses with `machine-fresh-workload-running-unproven` unless the containment
   subject is `Populated`. `echo ...; exit 7` can exit before that sample. If
   so, it is a separate gap in `start`, not in these reads.
3. **Non-TTY stderr is not returned.** The existing piped collector reads the
   helper's stdout only, so `logs.stdout` is the workload's stdout and `stderr`
   is always empty. With a TTY the pty already merges both. The live spec reads
   only stdout.
4. **A still-running workload at the deadline makes the outcome unknown** (see
   latching): there is no non-blocking exit read on the CPU V2 route.
