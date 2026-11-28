# Container fresh route: engine helpers had no usable home

- **Status:** helper environment FIXED in source 2026-11-27 (unit specs only), extended the same day with
  `XDG_RUNTIME_DIR` and `PATH` (section "Runtime directory and PATH"). The guest unit's own
  environment is OPEN (section "Guest unit"). Nothing here was run in the guest.
- **Component:** `src/lib/nogc_sync_mut/io/linux_fresh_epoch_launch_v1.spl`
  (`linux_fresh_epoch_project_launch_v1`), custody account check
  (`src/lib/nogc_sync_mut/io/linux_fresh_epoch_native_v1.spl`), guest provisioning
  (`scripts/check/check-linux-orchestrator-host-qemu.shs`).
- **Found while** checking item 6 of `container_fresh_route_exited_start_settlement_2026-11-27.md`.

## What the helpers got

Not `HOME=/nonexistent`. Every engine helper of the fresh route is launched from
`linux_fresh_epoch_project_launch_v1`, which built the request with `environment: []`, and the group
runtime passes exactly that list to `execveat` (`rt_lg_start_mode_v2`). `HOME=/nonexistent` is a rule for
the **broker's inherited** environment (`linux_fresh_epoch_broker_environment_v1`), not for the helper.

With no `HOME` the engine takes the home from the account record. Custody requires that record to say
`/nonexistent` (`epoch_native_accounts_v1`) and that path to be absent (`epoch_native_no_user_bus_v1`).
So on an account custody accepts, every helper would exit 1.

## Measurements (host, podman 4.9.3 rootless, uid 1000)

| Helper environment | Result |
|---|---|
| empty, account home exists | exit 0. `strace`: opens `/etc/passwd`, then `newfstatat("<account home>", AT_SYMLINK_NOFOLLOW)` three times. |
| `HOME=/nonexistent` | exit 1, `cannot resolve /nonexistent: lstat /nonexistent: no such file or directory` (`version`, `load`). |
| `HOME=<private existing dir>` only | exit 0 for load, create, start, inspect, stop, rm. Entries under that directory afterwards: 0. |
| `HOME=<run root>` only | exit 0; the run root's top level gains no entry. |

Not measured: an empty environment with an account home of `/nonexistent`. `bwrap` could not set up a
user namespace on this host, so the account record could not be replaced. The `strace` line above shows
the same `lstat` on the account home, so the outcome is expected to be the `HOME=/nonexistent` row.
`pull` was not measured either (no network use in these runs).

## Fix

`linux_fresh_epoch_helper_environment_v1(run_root)` returns `["HOME=" + run_root]` and the projection uses
it. The run root exists, custody holds it, and it is already the helper's directory, `--runroot` and the
parent of `--tmpdir`. A run root that is not one canonical absolute path is refused with
`fresh-epoch-helper-home-unsupported`. The broker rule is unchanged.

Every launch bound through custody takes this projection, workspace helpers included
(`fresh_workspace_bind_v3` and the primary attach go through `bind_profiled_launch_v1`), so they get the
same `HOME`. The stream policy's environment pin (`container_stream_policy_template_pin_v2`) compares the
policy with the Host's own template, not with the projected launch, and is not affected.

Spec: `test/01_unit/lib/container/linux_fresh_epoch_helper_environment_v1_spec.spl` (red: executed=0, the
function did not exist; green: 3 of 3). It tests the function and pins the projection's source line. No
passing spec executes `linux_fresh_epoch_project_launch_v1`: the three that reach it
(`linux_fresh_admitted_workload_v2_spec`, `linux_fresh_epoch_admission_v1_spec`,
`machine_fresh_epoch_lifecycle_v1_spec`) fail on the base commit and fail the same cases after.

## Runtime directory and PATH (decided and fixed in source 2026-11-27)

`linux_fresh_epoch_helper_environment_v1(run_root)` now returns
`["HOME=<run root>", "XDG_RUNTIME_DIR=<run root>", "PATH=/usr/bin:/bin"]`.

Measured (podman 4.9.3 rootless, uid 1000, private store, user bus made unreachable, each helper in its own
cgroup that is killed after it):

| Helper environment | Result |
|---|---|
| `HOME` only, a pause process already running for the uid | exit 0; `pause.pid` is `/run/user/1000/libpod/tmp/pause.pid`. This is what the HOME-only row above measured without knowing it. |
| `HOME` and `XDG_RUNTIME_DIR=<private dir>`, no `PATH` | every command exits 125: `command required for rootless mode with multiple IDs: exec: "newuidmap": executable file not found in $PATH`. |
| `HOME`, `XDG_RUNTIME_DIR=<run root>`, no `PATH` | the same exit 125. |
| `HOME`, `XDG_RUNTIME_DIR=<run root>`, `PATH=/usr/bin:/bin` | exit 0 for load, create, start, inspect, logs, stop, rm. `pause.pid` is `<run root>/libpod/tmp/pause.pid`. The run root gains `containers`, `libpod` and `runc` beside `networks`, `tmp` and the `vfs-*` entries it already gets. |

- **`XDG_RUNTIME_DIR`: needed.** Without it the pause process file is outside custody and shared by every
  store of the uid. The guest masks `user@<uid>.service`, so `/run/user/<uid>` is not expected to exist
  there; where podman then falls back to was not measured, and with the variable set it does not matter.
- **`PATH`: needed.** A helper that finds no pause process to join must make its user namespace, and looks
  `newuidmap` up through `PATH`. The route kills every helper's group, so that is the normal case. The
  value is the one the broker rule already requires of the broker.
- The offline store inventory still requires an empty run root before first use; these entries appear
  only once a helper ran, like the `vfs-*` ones.

## Guest unit (open, owner decision)

Read from source; `simple-orchestrator-host.service` was not started for this.

- The account is made with `useradd --home-dir /var/lib/simple-host --create-home`. Custody's account
  check wants `/nonexistent` in that field, so custody is expected to refuse with
  `fresh-epoch-native-service-account` before any helper is launched.
- The broker rule allows `PATH=/usr/bin:/bin`, `HOME=/nonexistent` and a short closed list. The unit
  carries `Environment=SIMPLE_HOST_EXEC=...` and an `EnvironmentFile` of `SIMPLE_*` keys, and systemd adds
  the account home as `HOME` and its own default `PATH`. Each of those is refused as
  `fresh-epoch-inherited-broker-environment-unsupported:<key>` at the first launch.

Changing the account home to `/nonexistent` would satisfy custody and, with the fix above, the helpers,
but the same account also runs the guest's other podman lanes. Whether those depend on the account home
was not checked. The `SIMPLE_*`
keys are how the acceptance spec is configured. Both are the unit owner's call: a second account for the
fresh route, or a different way to hand the spec its configuration. Not changed here.

### Audit 2026-11-28 (read from source, nothing started in the guest)

Unit and account are made by `guest_provision_script` in
`scripts/check/check-linux-orchestrator-host-qemu.shs`
(`run-orchestrator-native-qualification.shs` only calls that script).

| What | Guest today | What custody and the broker rule require | State |
|---|---|---|---|
| Account shell | `/usr/sbin/nologin` | `/usr/sbin/nologin` or `/sbin/nologin` | consistent |
| Account name, uid, gid | `simple-host`, 950, 950; the profiles are generated from them | `serviceName`, `serviceUid`, `serviceGid` | consistent |
| Account home | `/var/lib/simple-host`, created | `/nonexistent`, absent (`fresh-epoch-native-service-account`) | **open, owner decision** |
| Unit `HOME`, `PATH` | not set; systemd gives the account home and its own default `PATH` | `HOME=/nonexistent`, `PATH=/usr/bin:/bin` | **open**, follows the account |
| Unit extra environment | `EnvironmentFile` of 16 `SIMPLE_*` keys and `Environment=SIMPLE_HOST_EXEC=` | closed list; each is `fresh-epoch-inherited-broker-environment-unsupported:<key>` | **open, owner decision** |
| Unit `XDG_RUNTIME_DIR` | not set (the user manager is masked) | absent is allowed; when present it must be the run root | consistent |
| Run root `/run/simple-host/podman` | named by the generated profile; no `RuntimeDirectory=` and no `install -d` in the provisioning | must exist and be held by custody | **open**: who creates it on a fresh boot was not found |
| Helper environment | set by the projection itself, not by the unit | `HOME` and `XDG_RUNTIME_DIR` = run root, `PATH=/usr/bin:/bin` | consistent, independent of the unit |
| Unit file name | `${UNIT}` with no assignment since 3daa49c1dcd; under `set -eu` a fresh provisioning stopped at that line | `simple-orchestrator-host.service` (`hostUnit` of the generated profile) | **fixed 2026-11-28**: the assignment is back. Syntax-checked only; no guest was provisioned |

TODO (guest, not a PASS):

- Provision a fresh guest with the restored `UNIT=` line and read the unit back (`--verify`).
- Decide the account home and the `SIMPLE_*` hand-over (second account or another configuration route),
  then start the unit and take the first fresh-route launch past custody's account and environment checks.
- Find or add what creates the run root before first use.
