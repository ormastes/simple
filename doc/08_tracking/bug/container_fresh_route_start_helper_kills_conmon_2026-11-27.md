# Container fresh route: retiring the start helper kills the workload's conmon

- **Status:** OPEN. Found 2026-11-27 from source plus a host emulation with real podman. Not observed
  in the guest: no installed custody on this host.
- **Component:** Linux Podman fresh install route, helper containment
  (`src/runtime/runtime_linux_group_owner_impl.h`, `rt_lg_poll`), engine command line
  (`src/lib/nogc_sync_mut/io/linux_fresh_workload_launch_v2.spl`).
- **Spec cases affected:** every `live_run_v1` case of
  `test/03_system/app/container/feature/podman_shared_api_live_spec.spl` whose workload is still
  running when the start helper is reaped, and every case after it in the same store.
- **Found while** deciding the pause process question of
  `container_fresh_route_exited_start_settlement_2026-11-27.md` (Edge 3).

## Symptom (host emulation)

Rootless podman 4.9.3, each podman command in its own cgroup that is killed with `cgroup.kill` after the
command exits (what `rt_lg_poll` does once the helper leader is reaped; the route reaches it through
the broker's monitor loop, `native_linux_group_monitor_lease_v1`), the route's global flags,
`--network=none --cgroups=enabled --cgroupns=private --pid=private --cap-drop=ALL
--cgroup-parent=<delegated>`, no usable user bus, `busybox sleep 60`:

- `start` exits 0. Left in its cgroup: `catatonit` and `conmon`. Both die with the kill. The workload
  process (`sleep`) is alone in `<delegated>/libpod-<id>` and keeps running.
- Every later command (`container inspect`, `stop`, `rm`, a `create` of another container, `rmi`)
  exits 1 with

  ```
  invalid internal status, try resetting the pause process with "podman system migrate":
  could not find any running process: no such process
  ```

  The store still records a running container, its conmon pid is dead and there is no pause process, so
  the engine cannot rejoin its user namespace. This lasts until the stored state is repaired.

A workload that has already exited when the start helper is reaped (`/bin/true`, three runs, one with
`INVOCATION_ID` set) is not affected: `inspect` says `stopped`, stop and rm exit 0 and
`container exists` exits 1. That is a race the
workload wins only by being very short.

## Why

- Podman forks conmon from the `start` command, so conmon begins in the helper's group cgroup.
- With the cgroupfs manager podman then tries to move conmon to `<cgroup-parent>/conmon`. Rootless, that
  fails, logged at info level and therefore hidden by `--log-level=error`:

  ```
  Failed to add conmon to cgroupfs sandbox cgroup: creating cgroup path <delegated>/conmon:
  open /sys/fs/cgroup/cgroup.subtree_control: permission denied
  ```

  The engine walks from the cgroup root and writes `cgroup.subtree_control` on the way; an unprivileged
  uid cannot write the root's. The delegated subtree being writable does not help. The guest's service
  uid is unprivileged in the same way.
- `rt_lg_poll` kills a populated group as soon as its leader is reaped. For a detached `start` the
  leader exits at once and conmon is what is left.

## Options (not decided)

1. Keep the start helper's group as the workload's engine group: do not kill it at leader reap, hold its
   descriptor on the workload record, kill and collect it after Remove and Absence. It needs a new
   retirement mode in the group runtime, a place for the held group in the cohort census and partition
   population (today both refuse any occupant), and it changes the premise of Edge 3.
2. Make the engine's own move succeed, so conmon lands in `<delegated>/conmon`. Not possible for an
   unprivileged uid with podman 4.9's cgroupfs path creation; a newer engine may differ.
3. Keep `podman start` attached, so the helper leader lives as long as the workload. Changes what a
   retired start helper means for every later action.

## Acceptance

A workload that outlives its start helper can be inspected, stopped and removed through the route, and
its destroy settles, with no process the owner cannot account for.
