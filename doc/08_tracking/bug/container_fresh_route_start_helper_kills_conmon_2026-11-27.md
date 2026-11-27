# Container fresh route: retiring the start helper kills the workload's conmon

- **Status:** OPEN. Design decided 2026-11-27 (section "Decision"); **not implemented**. Found from source
  plus a host emulation with real podman. Not observed in the guest: no installed custody on this host.
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

## Measurements (2026-11-27, host, podman 4.9.3 rootless, uid 1000, busybox:1.36)

Emulation: a `Delegate=yes` user scope holding `deleg/` (the engine's `--cgroup-parent`, controllers
enabled) and `helpers/hN` (one group per command, `cgroup.kill` once the command returned, then `rmdir`).
Private `--root`/`--runroot`/`--tmpdir`, vfs, no usable user bus, the route's create flags. Every store,
container and cgroup was removed after each run.

| Candidate | Result |
|---|---|
| Baseline (every helper group killed) | `start` 0; `catatonit conmon` die with the group; `inspect`/`stop`/`rm` exit 1, `invalid internal status`. Reproduced. |
| `--cgroups=no-conmon` | Same as baseline: conmon stays in the start helper's group and dies with it. |
| `--cgroups=split` (with and without `INVOCATION_ID`) | `create` exits 125: `cannot specify --cgroup-mode=split with a cgroup-parent`. |
| `--cgroup-manager=systemd`, no user bus | `start` 0, conmon still in the helper group, dies, store broken. |
| conmon wrapper (`--conmon <script>` that writes its pid into an owner-made `deleg/conmon-a`, then execs conmon) | Works: `inspect` running, `stop`/`rm` 0; the group empties itself after a self-exit (`sleep 3; exit 7`). Needs an installed executable and a `--conmon` option the launch projection refuses on purpose. |
| `start --attach` (leader lives as long as the workload) | Works: `inspect` running while attached, `exited 0` after. The helper is then not retired until the workload ends. |
| Held group: `start` cloned into an owner-made `deleg/engine-a` that is not killed at leader reap | Works for two containers side by side: `inspect` running, workload alone in `deleg/libpod-<id>` with `memory.max=67108864`, `logs`/`stop`/`rm` 0, `container inspect` then 125 (absent). |
| Freeze and move: ordinary helper group; at leader reap `cgroup.freeze=1`, wait `frozen 1`, write each member pid to `deleg/engine-a/cgroup.procs`, then retire the helper group as today | Works, three containers: helper group reports `populated 0` before its kill, moved members are thawed (`cgroup.freeze` 0 in the engine group), every later command exits 0. |

What stays in the surviving group (held and moved alike):

- `conmon` until the workload ends, then it leaves by itself (a fast exit showed `conmon podman runc` for an
  instant, nothing one second later).
- `catatonit` (the rootless pause process) **when the start helper was the one that created it**. It never
  leaves by itself: it was there after `stop`, after `rm` and after a self-exit. With a pause process in an
  engine group, later helpers join it instead of making their own.
- The start helper's pipes are not held: `start` through a pipe gave EOF after 0.16 s; `conmon` and
  `catatonit` have `/dev/null` on fd 1 and 2.

Killing the engine group **while the store still records a running container** poisons the store for good:
with the workload cgroup killed as well, `inspect`, `stop`, `rm`, `rm -f`, `container inspect` and a
`create` of another container all exit 1 with the same `invalid internal status`. After `stop`, `rm` and
the absence check, killing it is harmless (the next helper makes a new pause process).

## Decision

**An owner-held engine group per started container, filled by freeze-and-move at the start helper's leader
reap.** The helper's group is retired exactly as today; what the reaped `start` leader left behind is moved,
not spared, and the owner holds the destination by its cgroup.

1. The engine group is `<delegatedCgroup>/simple-engine-<start helper identity>`, beside `libpod-<id>` and
   the `simple-parent-*` helper parents (`delegated_cgroup_path` is both the engine's `--cgroup-parent`
   and the broker's delegation root, `linux_fresh_epoch_launch_v1.spl`). The move therefore needs no
   permission the engine's own placement of the workload does not already need.
2. Only the Start launch asks for it, and only a leader that exited 0 without a timeout or a cancel gets it.
   Every other outcome and every other helper is killed as today; the pinned kill in `rt_lg_poll` stays and
   also catches anything that was not moved.
3. Membership is the only selector: every member of the helper group at leader reap is moved. Nothing is
   chosen by name, pid file or engine text. The group is frozen first, so nothing can fork between the read
   and the move.
4. The owner opens the group by name under its retained delegated handle, records device and inode, and
   holds the descriptor on the workload record. No process then survives a helper outside a cgroup the
   owner holds: the workload in `libpod-<id>` (the associated subject, as today) and the engine's monitor
   and pause process in the engine group.
5. The engine group is killed, observed `populated 0` and removed at three places, each before any cohort
   census: the subject settle, the exited-start settle (a fast exit leaves `catatonit` there, so without
   this the census refuses on every retry), and the transfer `close_v2`.
6. Two orders. An ordinary destroy kills the group strictly after the owner's own completed Stop, Remove
   and Absence; before that it refuses with a named reason
   (`machine-fresh-workload-engine-group-store-live`), because the kill would poison the store. Epoch
   teardown kills regardless and records that the store is then unusable.

### Why not the others

- **Keep the start helper's group alive (option 1 below).** Works on the host, and it would need no new
  kill: the broker's existing cancel retires the group. But it makes one helper immortal, and the owner is
  built around one helper at a time. Read: the lifecycle has a single helper slot (`capture_v2` overwrites
  `process`), and `action_begin_v2` refuses a new action while another helper cohort is live
  (`workspace-primary-helper-cohort-active`, `machine-probe-helper-cohort-active`); `helper_retired` is
  "that slot is empty", which the exited-start settle relies on. Read, and against this reason: the
  delegated parent is `simple-parent-<identity>`, one per helper, so a second helper is not blocked there.
  Not checked: whether the capacity receipt and the helper sub-charge of a broker that never finishes
  block or miscount later helpers. Freeze-and-move leaves the helper's whole lifetime as it is.
- **Attached start (option 3).** The helper's timeout would then kill a live workload's monitor, the
  workload's output would flow through the helper's pipes, and every later action would run beside an
  unretired helper.
- **A conmon wrapper.** Needs a second installed executable and a conmon option; the launch projection
  refuses conmon and runtime configuration routes by design, and the installer is a separate owner.
- **Engine settings (option 2).** `split` is refused with a cgroup parent; `no-conmon` and the systemd
  manager leave conmon where it was. Nothing in podman 4.9.3 moves conmon for an unprivileged uid.

### What it changes in #12234's chain

Links 1, 3, 4 and 5 of `machine_fresh_engine_residue_containment_v3_spec.spl` stay true. Link 2 gains one
exception, the moved residue of a successful Start, and the pause-process decision of
`container_fresh_route_exited_start_settlement_2026-11-27.md` (Edge 3) changes from "it cannot outlive its
helper" to "it outlives only a Start helper, inside the engine group, which is killed before the census".
The pin and both records must be updated in the same change that turns the move on.

## Implementation order (one chain, closed at both ends)

Nothing below is built. The retirement side comes first and the line that requests the move for Start
comes last, so no commit can leave a group nobody kills.

1. Owner side: an engine-group holder next to the subjects in `linux_fresh_workload_native_v2.spl` (open by
   name under the delegated handle, identity recheck, kill, `populated` read, remove); a record field for
   its identity; the three retirement sites and the two orders above; pure reducer for the order with the
   named refusals, spec first.
2. Runtime: in `runtime_linux_group_owner_impl.h`, on `leader_reaped && populated` for a launch that asked
   and whose leader exited 0: make the group under `rt_lg_delegation.root_fd`, freeze, move, then fall
   through to the existing kill. Carry the request as one more profile word so no `rt_*` symbol is added
   and every other launch stays byte-identical (`rt_lg_profile_parse_v3` takes exactly 12 words today; the
   Rust seed only registers signatures, `codegen/runtime_sffi.rs`). Prove it with a C selfcheck beside
   `src/runtime/test/runtime_linux_group_start_ownership_selfcheck.c`, run in a delegated user scope.
3. Protocol: the extra word on the Start launch only (`group_process_stream_profile_v3.spl`,
   `linux_fresh_workload_launch_v2.spl`), part of the launch identity.
4. Last: the Start action requests the move and captures the group; update the residue pin and the two
   records.

## Open

- Not implemented (above). The route still breaks every workload that outlives `start`.
- Cost not in the measurements: the owner cannot kill a cgroup today. Containment is capture, observe and
  close (`linux_container_containment_v1.spl`); the only kill is the broker's, for its own helper group.
  Step 1 of the build order therefore adds an owner-side kill and remove, which the held-group option
  would not need.
- Environment of the measurements: every candidate ran with `PATH`, `HOME` and `XDG_RUNTIME_DIR` set. The
  route's helpers had none of them (now `HOME` only, see the HOME record). Held start, inspect, stop and
  rm were repeated with an empty environment and with `HOME` only and behaved the same; freeze-and-move,
  the wrapper, attach and the forced kill were not repeated that way.
- The engine group has no limits of its own in the measurements. Decide whether it gets a small
  `memory.max`/`pids.max` and which charge it belongs to; its use was not measured.
- A failed Stop leaves a store that says running. Ordinary destroy then refuses (item 6) and only teardown
  can clear it; whether the route should repair the store instead is undecided.
- Guest: nothing here was run in the guest. The helper `HOME` and the unit's environment are in
  `container_fresh_route_helper_home_2026-11-27.md`.
- A newer engine may place conmon itself; not checked beyond 4.9.3.

## Options as first listed

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
