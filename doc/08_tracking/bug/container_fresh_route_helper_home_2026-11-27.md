# Container fresh route: engine helpers had no usable home

- **Status:** helper environment FIXED in source 2026-11-27 (unit specs only). The guest unit's own
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

Still open for the helper: it has no `XDG_RUNTIME_DIR`. Where the engine then keeps its runtime files
(`pause.pid` among them) for an account without `/run/user/<uid>` was not measured; on this host it used
`/run/user/1000/libpod`, outside the run root.

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
