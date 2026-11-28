# Container fresh route: retiring the start helper kills the workload's conmon

- **Status:** BUILT IN SOURCE 2026-11-27 (section "Built"), the whole chain in one commit; workspace starts
  added the same day (section "Workspace starts"). Proven by unit
  specs, a C selfcheck on real cgroup v2 groups and a host emulation with real podman. **Not run in the
  guest**: no installed custody on this host, and the installed broker has to be rebuilt first.
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

Built as listed; see "Built". The retirement side comes first and the line that requests the move for Start
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

## Built (2026-11-27)

In the order above, one commit.

1. **Owner side.**
   - Order reducer `machine_fresh_workload_engine_group_v3.spl`: nothing to retire for an owner that never
     asked; refuses `machine-fresh-workload-engine-group-helper-active` while a helper is live and
     `machine-fresh-workload-engine-group-store-live` until the owner's own Stop, Remove and Absence all
     completed; `machine-fresh-workload-engine-group-retained` gates all three settle preparations
     (subject, exited start, probe), `close_native_v2` and `closed_v2`, so the charge is kept while a group
     is recorded. The finite probe lane never stops its payload; there, and only there, the owner's own
     completed `probe-wait` stands in for Stop.
   - Holder `linux_fresh_engine_group_v3.spl`, called from `workload_engine_group_v3` in
     `linux_fresh_workload_native_v2.spl` under the retained delegated descriptor (handle 1, the one the
     subjects use): open by fixed name, cgroup2 and directory check, recorded-identity check
     (`fresh-workload-engine-group-replaced`), `cgroup.kill`, up to 200 `cgroup.events` reads 5 ms apart
     (`fresh-workload-engine-group-still-populated` at the bound, retryable), `rmdir`, absence read back.
     An absent group is retired by that observation. This is the route's only owner-side kill.
   - Record fields on the lifecycle state: `engine_groups` (launch identities, at most four) and
     `engine_group_objects` (the statx identity custody reported for each). Set in `capture_v2` from the
     launch that was actually captured, so they exist before any outcome of the helper is known.
   - Four sites, each before the settle or the census: the `destroy` action
     (`fresh_epoch_workload_v2.spl`, after Absence, before either settle; `settle_v2` and the pinned
     `machine_fresh_workload_settle_cpu_v3` are byte-unchanged and refuse through the gate),
     `machine_fresh_workload_settle_exited_start_v3` (before `observe_probe_absence_v3`), the transfer
     `close_v2` (before `close_native_v2`), and a fourth the decision did not list:
     `machine_fresh_probe_settle_v3`. A probe-lane owner starts its container through the same Start
     projection and settles on the same cohort census, so without it a pause process left in the engine
     group would refuse that census on every retry. The spec pins that these two are the only callers of
     the census.
2. **Runtime.** `rt_lg_move_residue_v3` in `runtime_linux_group_owner_impl.h`, called once from
   `rt_lg_poll` immediately before the pinned kill, only for `exit_code == 0` with no timeout, cancel or
   pending kill. Freeze, wait for `frozen 1` (200 reads, 5 ms apart), `mkdirat` the engine group under
   `rt_lg_delegation.root_fd` (an existing directory is never adopted), write every line of the frozen
   group's `cgroup.procs` to the engine group, require the helper group's `cgroup.procs` to read empty. Any
   failure kills the engine group it made and removes it. No `rt_*` symbol was added.
3. **Protocol.** `GroupProcessStreamProfileV3.leader_residue_mode`, `""` or `move-to-engine-group-v1`. It
   is one more wire field and a thirteenth runtime word, both present only when set, so every other launch,
   its digest and its twelve words are byte-identical. `rt_lg_profile_parse_v3` takes twelve words, or
   thirteen whose last is 1. An installed broker built before this refuses a sixteen-field profile
   (`trailing wire fields`), so an old broker cannot silently skip the move.
4. **Request.** `linux_fresh_workload_project_launch_v2` sets the mode for `Start` and clears it for every
   other action, whatever the base carried. The residue pin gained link 2a; Edge 3 of the settlement
   record and the HOME record are updated.

### Changes to the decision, made while building

- **No descriptor is held between calls** (item 4 said one is held on the workload record). The owner
  holds the name and the recorded device and inode instead, and re-opens under the retained delegated
  descriptor on each call. A replaced directory is detected the same way; a descriptor on a record that
  is copied by value has no single closer.
- **The second order (epoch teardown kills regardless) is not built** (item 6). Nothing in the route closes
  an unsettled workload today: `close_native_v2` refuses with `machine-fresh-workload-charge-retained`, and
  no owner code kills `libpod-<id>` either. An engine group whose owner is latched is therefore **retained
  and refused**, exactly like its workload: no settle, no close, and a new epoch's census refuses while its
  processes live. Clearing both is the operator's teardown of the delegated subtree, as before.
- **Limits: none of its own.** The engine group inherits the delegated root. Measured after `stop` and `rm`
  of one container: `memory.peak` 11.2 to 11.9 MB and `pids.peak` 13 to 18, which is the engine's own
  `container cleanup` run by conmon at exit, on a 20-CPU host. A limit set too low kills the monitor of a
  container the store calls running, which is the poisoning this change exists to prevent; the group's
  use is bounded by the partition's own limits like every other child of the delegated root. It is not a
  sub-charge of the workload record.
- **Helper environment.** Helpers now also get `XDG_RUNTIME_DIR=<run root>` and `PATH=/usr/bin:/bin`. See
  the HOME record: without a pause process to join and without `PATH` every helper exits 125.

### Host measurements (podman 4.9.3 rootless, uid 1000, busybox:1.36, 2026-11-27)

A `Delegate=yes` user scope with `deleg/` and `helpers/hN`, private `--root`/`--runroot`/`--tmpdir`, vfs,
the route's flags, helper environment `HOME`, `XDG_RUNTIME_DIR`, `PATH` only, user bus made unreachable
(`DBUS_SESSION_BUS_ADDRESS` pointing nowhere; without that podman moved its pause process into a systemd
scope outside the emulation). Everything created was removed.

| Question | Result |
|---|---|
| Does a long-running workload survive `start`, and do later commands work? | Yes. Two containers (`sleep 300`): start helper A left `catatonit conmon`, B left `conmon`; both moved, helper groups `populated 0` before their kill; `inspect` (running), `logs`, `stop`, `rm` exit 0; absence exits 125. |
| Is the kill gate per container enough when the pause process sits in A's group? | Yes. After A's Stop, Remove and Absence, A's group (holding the pause process) was killed while B ran: B's `inspect`, `stop`, `rm` exit 0. Each later helper made a new pause process in its own group. |
| Does anything remain after settle? | No. Both engine groups killed, `populated 0`, removed; `deleg/` and `helpers/` had no child and no process. |
| Crash between freeze and move (one of two members moved, then nothing) | The frozen helper group is emptied by `cgroup.kill` and removed. The partial engine group is found by name alone, killed and removed. The store is then poisoned for that container (`invalid internal status`), so its owner cannot run Stop: retained and refused, as above. |
| Same with `XDG_RUNTIME_DIR` unset | `pause.pid` is `/run/user/1000/libpod/tmp/pause.pid`; helpers joined a pause process that was already there, outside every group of the emulation. |

The runtime move itself is proven by `src/runtime/test/runtime_linux_group_residue_move_selfcheck.c`
(`sh scripts/check/check-linux-group-residue-move.shs`, six cases on real groups: moved and thawed; leader
failed; not asked; cancelled; name already taken; frozen group still killable).

## Workspace starts (2026-11-27, follow-up)

The gap listed under "Open" until this change: `linux_fresh_workspace_project_launch_v3` is a separate
projection and passed the base profile through, so a workspace container that outlived its start helper
lost its monitor. Source only, like the rest; not run in the guest.

- **Request.** The workspace projection now sets `leader_residue_mode` for `Start` and clears it for every
  other action, whatever the base carried, in the same statement as the plain projection. Before, a mode
  carried by a caller's template would have passed through to every workspace helper.
- **Record and observe: nothing new.** A workspace action runs through the same
  `machine_fresh_workload_begin_v3` / `machine_fresh_workload_progress_v3` (the workspace workflow calls
  both), so `capture_v2` records the group from the captured launch and the `start` completion observes
  its device and inode.
- **Fifth retirement site.** `machine_workspace_settle_v3` retires the engine group after its settled early
  return and before both workspace settles (plain and retained). Both pass the `prepare_settlement_v2`
  gate, and the retained one commits its native retirement before reaching that gate, so the retirement
  has to come first; a refusal there writes nothing, which is what the service stages
  (`host_linux_service_agent_v4`, `host_linux_service_remote_build_v4`, stage `settle`) already assume when
  they resume on the next call. The order is unchanged: the workspace Destroy runs the owner's own Stop,
  Remove and Absence. The transfer `close_v2` attempt (site 3) is shared. `close_workload_v3` makes no
  attempt of its own and needs none: it refuses through the same gate while a group is recorded, and a
  group is only still recorded when the settle that retires it has not passed.
- **A settle called before Destroy finished** now refuses `machine-fresh-workload-engine-group-store-live`
  (or `...-helper-active` while a helper is live) when a group is recorded, where it refused
  `machine-fresh-workload-absence-unproven` before. All are plain refusals and nothing is latched.

### Other start-like paths

| Path | Leaves a long-lived process under a helper group? | Done |
|---|---|---|
| Workspace start, TTY arm (`create --tty --interactive`, agent) | Yes, the same `start -- <id>`: `catatonit conmon` at leader reap. | Covered by the request above. |
| Workspace start, no-TTY arm (remote build) | Yes, the same. | Covered. |
| Plain start with build roots or `--tty` (#12209, `workloadBuildRootPrefix`) | Yes. | Already covered: it goes through `linux_fresh_workload_project_launch_v2`. |
| Workspace primary attach (`attach --detach-keys= --sig-proxy=false`) | No. The leader lives as long as the transport and forks no monitor. It is built on the Inspect projection (`fresh-workspace-primary-attach-inspect-identity-required`), which clears the mode. | Pinned, not changed. |
| `wait` / `logs` probes | No. Finite readers built on a verified Inspect projection. | Unchanged. |
| Secondary exec, TTY or not (`LinuxOciEngineExecOwnerV3`) | No helper group at all: it talks to the installed engine socket (`local_unix_connect_v1`). The exec session's monitor belongs to that service. | Does not apply. |
| Epoch startup V1 (`linux_fresh_epoch_project_launch_v1`) | Its operand allow-list admits `start` and `exec` from the caller's template. Its entry `local_container_service_start_fresh_epoch_v1` takes the template from its caller and has no caller in `src/` today. | **Built in source 2026-11-28**, see "Edges closed". `start` asks; `exec` and every other operand do not. |

### Host measurement (podman 4.9.3 rootless, uid 1000, busybox:1.36, same emulation)

The route's create flags plus the workspace ones (`--userns=keep-id --user=1000:1000 --workdir /workspace
--mount type=bind,...,rw,nosuid,nodev,bind-propagation=rprivate`), `sleep 300`. Everything was removed.

| Case | Result |
|---|---|
| TTY arm, start helper group killed at reap (before) | `start` 0, left `catatonit conmon`; `inspect`, `stop`, `rm`, absence all exit 1, `invalid internal status`. |
| TTY arm, residue moved | 2 members moved, helper group `populated 0`; `inspect` running (`tty=true stdin=true`), `stop`, `rm` exit 0, absence 125; engine group then held `catatonit`, killed, `populated 0`, removed. |
| No-TTY arm, residue moved | The same (`tty=false stdin=false`). |
| TTY arm, residue moved, then an attach helper killed by `cgroup.kill` while attached | The attach group held one `podman`; after its kill `inspect` running, `stop`, `rm` 0, absence 125. |

### Proof

`test/01_unit/lib/container/linux_fresh_workspace_start_residue_v3_spec.spl` executes the production
workspace projection (Start asks and yields the thirteenth word; every other action is cleared and a plain
base stays byte-identical) and pins the settle order and the paths in the table. Red before the source
change (2 of 6), green after (6 of 6). `machine_fresh_engine_residue_containment_v3_spec.spl` link 2a and
`machine_fresh_workload_engine_group_v3_spec.spl` (five sites) were updated in the same change.

## Edges closed (2026-11-28)

Source and unit specs only. Nothing here was run in the guest or against a live engine; the rows under
"TODO" are what that still needs.

### Epoch startup V1 asks, and the epoch close retires

- **Retirement first.** The epoch lifecycle records the launch identity of a provider helper whose captured
  launch asked (`attach_process_v1`, before the template check; the unattached cleanup records it as well).
  `MachineFreshEpochAdmissionOwnerV1.close_v1` retires `simple-engine-<identity>` through the custody it
  already holds, after `close_process_v1` and before the writer and custody are released. A refusal is plain
  (nothing latched, the same close may be repeated) and `closed_v1` refuses
  `machine-fresh-epoch-engine-group-retained` while a group is recorded.
- **This is the second order of the decision (item 6)**, built for the epoch helper only: the group is killed
  whatever the store records, because the epoch is ending and its store is not read again. The workload
  owners keep the first order (after their own Stop, Remove and Absence).
- **Request last.** `linux_fresh_epoch_leader_residue_mode_v1(provider, operation)`: `start` and a provider
  path ending in `/podman`, nothing else. The projection rebuilds the profile, so a mode carried by the
  caller's template never passes through. The `version` base the installed owner binds for every workload
  and workspace helper is byte-identical to before; binding a bound `start` again yields the same bytes, so
  `validate_profiled_launch_v1` still matches.
- `exec` from the epoch template is not changed: the exec session's monitor was not measured on this path.

### Live workload: Stop, Destroy, settle

No kill was added at Stop: the measurement above stands (killing before Remove and Absence poisons the
store). What was checked and pinned:

- Order with a live workload (pure reducer, executed): nothing completed, Stop only, and Stop plus Remove
  all refuse `machine-fresh-workload-engine-group-store-live`; all three with the Absence helper not yet
  collected refuse `...-helper-active`; then every recorded group is named, in recording order.
- A retired group is forgotten exactly once (`machine_fresh_engine_group_forget_v3`): a second retirement
  of the same name refuses `machine-fresh-workload-engine-group-unrecorded`, so a settle that follows a
  retirement can neither kill twice nor pass with a group still recorded.
- **Leak fixed.** `engine_group_retired_v3` removed the identity but kept the recorded device and inode in
  `engine_group_objects`. It now drops both.
- The bound of four groups does not fail silently: `capture_v2` latches the owner when a fifth identity
  cannot be recorded (read, not changed).

### A refused move is the Start's own failure

Before: `rt_lg_poll` discarded the result of `rt_lg_move_residue_v3`. When the delegated root refused the
engine group, the residue was killed with the helper group and the Start helper still reported exit 0, so
the owner saw a clean start of a container whose monitor was dead.

- Runtime: the move returns 0 or an exit code and `rt_lg_poll` stores it as the leader's.
  `RT_LG_RESIDUE_MOVE_PERMISSION_EXIT` 1001 for EACCES, EPERM or EROFS on `mkdirat` or on a member's
  `cgroup.procs` write; `RT_LG_RESIDUE_MOVE_FAILED_EXIT` 1000 for every other failure of a requested and
  attempted move (freeze, name already taken, a member that could not be moved). Both are above every wait
  status and inside the observation's exit bound (4294967295). A move that was never attempted (leader
  failed, timeout, cancel, nothing left) reports the leader's own code as before.
- Owner: `machine_fresh_engine_group_move_outcome_v3` names them, and the `start` completion latches
  `machine-fresh-workload-engine-group-move-permission` or `...-move-failed` ahead of the generic
  `machine-fresh-workload-command-failed`. The group stays recorded and is found absent at retirement.
- The residue is still killed: nothing may stay in the leader's group. The store of that container may
  then be poisoned, exactly as before; what changed is that the owner knows and says why.
- Selfcheck: seven cases. New: the name-taken case reports 1000; a root this uid may not create under
  reports 1001, makes nothing and kills the residue (skipped as root, exit 77).

### Proof (Rust seed interpreter, diagnostic; C selfcheck with clang on real cgroup v2)

| Spec | Before the source change | After |
|---|---|---|
| `linux_fresh_epoch_start_residue_v1_spec.spl` (new) | executed 6, failed 5 | executed 6, passed 6 |
| `machine_fresh_workload_engine_group_v3_spec.spl` (17 to 20 cases) | executed 20, failed 2 | executed 20, passed 20 |
| `machine_fresh_engine_residue_containment_v3_spec.spl` | executed 4, failed 2 | executed 4, passed 4 |
| `check-linux-group-residue-move.shs` | six cases | PASS, seven cases |

### TODO (seed-only or source-only evidence; none of these is a PASS)

| Item | Why it is not proven | Needs |
|---|---|---|
| Epoch close retires the engine group | The epoch lifecycle and admission close are stateful owners; the seed stops at the native origin check. Source pins only. `retire_engine_group_v3` goes through `borrow_workload_observer_v2` on the epoch's own custody, which no run has exercised before a workload transfer. | Guest: an epoch `start` whose container outlives its helper, then `close_v1`; the group must be gone and the close must pass. |
| Start latches the typed move refusal | The `start` completion is in the stateful effects; pinned by source, the classifier is executed. | Guest: a delegated root the broker cannot create under; Start must fail with `...-move-permission`. |
| Exit code 1001 reaches the owner | The runtime value is proven by the C selfcheck and the bounds were read (`linux_process_poll_decode_v1`, `group_process_observation_decode_v1`); the broker between them was not run. | Rebuilt broker in the guest. |
| Stop, Destroy and settle of a workspace whose workload is still running | Order and forget are executed as DATA; the workspace workflow is not. | Guest: agent or remote-build workload alive at start-helper reap, then Stop, Destroy, the `settle` stage twice (the second must be the settled early return). |
| `exec` from the epoch template | Not measured. | Host emulation of an epoch `exec` with the helper group killed. |

## Open

- **Guest.** Nothing here was run in the guest. It needs the broker and runtime rebuilt and installed
  (the wire field is refused by an older broker), then `podman_shared_api_live_spec.spl`.
  The workspace half needs a workspace run on top of that: an agent (TTY) or remote-build workload that is
  still running when its start helper is reaped, then Stop, Destroy and the `settle` stage.
- **The owner-side Simple code is not executed by any spec.** The seed cannot run the stateful owners
  (their first step is a native process-origin check, `unknown extern function: gettid`). The reducers and
  the protocol are executed; the lifecycle, effects, custody and holder are loaded and source-pinned only.
- ~~Workspace workloads are not covered.~~ Closed in source the same day, see "Workspace starts".
- **A failed Stop** leaves a store that says running. Destroy then refuses
  (`machine-fresh-workload-engine-group-store-live` is never reached; the Stop refusal comes first) and
  the group is retained with the workload. Whether the route should repair the store is undecided.
- **Permission of the move in the guest.** The broker writes into `<delegatedCgroup>/simple-engine-*`
  from its own scope; that needs the same write access to the delegated root's `cgroup.procs` that the
  engine's placement of `libpod-<id>` needs. True in the emulation, not checked in the guest.
  Since 2026-11-28 a refusal there fails the Start under its own reason instead of passing as a clean
  start ("Edges closed").
- A newer engine may place conmon itself; not checked beyond 4.9.3.
- `src/runtime/test/runtime_linux_group_start_ownership_selfcheck.c` does not compile at the base commit
  (`owned_adapter_fill_reserved_values` undeclared in its stub harness). Found here, not changed.
- `src/lib/source_inventory.lock` does not list the two new modules. It already lacks the modules added
  earlier the same day, and its checker could not run on this host (`interpreter rc=127`). Not changed.

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
