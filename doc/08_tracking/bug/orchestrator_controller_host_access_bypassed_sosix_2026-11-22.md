# Orchestrator controller host access bypassed SoSix (2026-11-22)

Status: fixed (controller); lib orchestration tier left as provider-side, see below.
Sibling of `doc/08_tracking/bug/orchestrator_client_host_access_bypassed_sosix_2026-11-22.md`
(PR #10809, client side). That record listed the controller leftovers; this
record closes them.

## Problem

`src/app/orchestrator/*.spl` (the controller, product code) reached the host
through raw SFFI and provider owners instead of the SoSix aliases. Found at
base `origin/release/1.0.0` `d3ee44d4e91`:

| file:line | raw route |
|---|---|
| `main.spl:2` | `std.sffi.cli_args.cli_get_args` |
| `caret_session_protocol_v1.spl:9` | `app.io.mod.{env_get, file_exists, file_read_regular_no_follow_bounded, file_atomic_write, dir_create_all}` |
| `caret_session_protocol_v1.spl:11` | `std.nogc_sync_mut.package_sffi.{set_permissions}` |
| `caret_session_service_v1.spl:9` | `app.io.mod.{getpid, file_exists, file_remove, dir_exists, dir_create_all, dir_list, dir_remove, dir_remove_all}` |
| `container_plan_prepare_v1.spl:3`, `remote_run_plan_v1.spl:6` | `app.io.mod.file_read_regular_no_follow_bounded` |
| `controller_gateway_v1.spl:3`, `remote_run_command_v1.spl:14` | `app.io.mod.{file_read_regular_no_follow_bounded, file_is_regular_no_follow}` |
| `controller_gateway_v1.spl:14` | `std.nogc_sync_mut.file_system.metadata.file_mode_bits` |
| `remote_run_command_v1.spl:15` | `std.nogc_sync_mut.io_runtime.file_read_bytes_result` |
| `remote_run_command_v1.spl:17`, `local_controller.spl:6` | `std.nogc_sync_mut.io.dir_ops.dir_is_real_no_follow` |
| `remote_run_v1.spl:57` | `app.io.file_ops.file_atomic_write` |
| `remote_run_v1.spl:58` | `std.nogc_sync_mut.io.dir_ops.dir_create_all` |
| `server_command_v1.spl:1`, `server_config_load_v1.spl:2` | `app.io.mod.{env_get, home, [file_exists,] file_read_regular_no_follow_bounded}` |
| `local_controller.spl:5` | `std.nogc_sync_mut.io.file_ops.{secure_temp_dir, file_create_exclusive, file_read_regular_no_follow_bounded}` |
| `agent_task_command_v1.spl:4`, `controller_service_command_v3.spl:7`, `execution.spl:7`, `explain.spl:7`, `host_identity_command_v1.spl:9`, `host_identity_profile_v1.spl:15`, `remote_build_port_install_v3.spl:17`, `validation.spl:9` | `std.nogc_sync_mut.io.file_ops.file_read_regular_no_follow_bounded` |
| `host_identity_command_v1.spl:11`, `server_ssh_transport_v1.spl:14` | `std.nogc_sync_mut.io.time_ops.time_sample_unix_micros_or_failure` |
| `server_ssh_relay_v1.spl:9` | `std.nogc_sync_mut.io.pipe.{Stdin, Stdout}` |

No `extern fn` or direct `rt_*` call existed in the controller.

## Change

Exact owner functions re-exported unchanged (same function, same name) from
the SoSix families that already own the capability, then the controller
imports switched to them:

- `sosix/host.spl` (args, files, env, pid already owned there): `cli_get_args`
  (raw argv — `main.spl` keeps its own stripping; NOT `sosix_get_cli_args`,
  whose launcher check differs), `file_read_regular_no_follow_bounded`,
  `file_is_regular_no_follow`, `file_atomic_write`, `file_remove`,
  `file_create_exclusive`, `secure_temp_dir`, `dir_exists`,
  `file_read_bytes_result`, `dir_create_all`, `dir_list`, `dir_remove`,
  `dir_remove_all`, `dir_is_real_no_follow`, `env_get`, `home`,
  `file_mode_bits`, `set_permissions` (provider owner stays `package_sffi`;
  no other SoSix mode-setting owner exists).
- `file_exists` / `getpid` call sites use the existing `sosix_file_exists` /
  `sosix_getpid` aliases (same `io.file_ops.file_exists` /
  `io.sysinfo_ops.getpid` functions `app.io.mod` re-exported). An unused
  `file_exists` import in `caret_session_service_v1.spl` was dropped.
- `sosix/time.spl`: `time_sample_unix_micros_or_failure`.
- `sosix/stdio.spl`: `Stdin`, `Stdout` from `io.pipe`.

Guard: `scripts/check/check-orchestrator-controller-sosix-only.shs` (globs
every `src/app/orchestrator/*.spl`; `--selftest` with clean / dirty /
allowed / empty fixtures; 0 files is ERROR).

## Left as-is, with reasons

- `std.nogc_sync_mut.io.tcp.{TcpStream, TcpListener}` (`caret_session_protocol_v1.spl:13`,
  `caret_session_service_v1.spl:13`): typed socket owners that themselves
  import `std.nogc_sync_mut.sosix.network` (`io/tcp.spl:11`). Re-exporting
  them from `sosix.network` would be an import cycle. They are already a
  client of SoSix, not a raw route.
- Domain owners under `io/` (`host_identity_store_v1`, `stdin_command_v1`,
  `host_service_auth_setup_v1`, `file_lock_owned_v2`, `local_authority_policy_v1`,
  `host_identity_ssh_projection*_v1`): typed protocol/state owners, not host
  primitives; out of the guard's scope by design.
- `src/lib/nogc_sync_mut/orchestration/host_execution_observation_v2.spl:11-13`
  (`io.file_ops`, `io_runtime.dir_create`, `sffi.fs.file_atomic_write_mode`):
  std library tier, not product code. Evidence: `sosix/host.spl:22` itself
  imports from `std.nogc_sync_mut.orchestration.*`, so routing orchestration
  through sosix would be a package cycle; and 71 of 115
  `orchestration/*.spl` modules import `io.*` / `io_runtime` / `sffi.*`
  directly. Changing one module would not be a coherent policy.

## Verification

- `sh scripts/check/check-orchestrator-controller-sosix-only.shs --selftest` -> `PASS — selftest (4 fixtures)`
- `sh scripts/check/check-orchestrator-controller-sosix-only.shs` -> `PASS — 41 orchestrator controller file(s) checked`
- Same check on the base tree (`git archive origin/release/1.0.0 src/app/orchestrator`) -> `FAIL — 28 raw host route(s) in 41 orchestrator controller file(s)`
- `sh scripts/check/check-no-direct-rt.shs --roots src/app/orchestrator` -> `PASS — 41 file(s) scanned ... forbidden=0`
- Not built or run (no bootstrap/native build on this host by request); the
  changes are import-path re-exports of the identical functions.
