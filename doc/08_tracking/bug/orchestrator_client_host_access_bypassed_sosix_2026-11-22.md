# Orchestrator client reached the host through app.io.mod, not SoSix (2026-11-22)

**Status:** fixed (this change). **Area:** `src/app/llm_caret` (caret orchestrator client).

## Problem

Owner bar: the orchestration client is pure Simple and depends on the host only
through SoSix. Both client files spawned the controller through the app IO facade,
which re-exports the provider owner `std.nogc_sync_mut.io.process_ops` directly:

- `src/app/llm_caret/orchestrator_client.spl:3` — `use app.io.mod.{process_run_bounded, process_bounded_timed_out}`
- `src/app/llm_caret/orchestrator_execution_client_v2.spl:4` — same import

The SoSix alias for the same implementation already existed
(`std.nogc_sync_mut.sosix.process.sosix_process_run_bounded`); the pure timeout
classifier `process_bounded_timed_out` had no SoSix alias.

## Fix

- `src/lib/nogc_sync_mut/sosix/process.spl`: add
  `process_bounded_timed_out as sosix_process_bounded_timed_out`.
- Both client files import `sosix_process_run_bounded` /
  `sosix_process_bounded_timed_out` from `std.nogc_sync_mut.sosix.process`.
  Same underlying functions, so behavior is unchanged.
- Guard: `scripts/check/check-orchestrator-client-sosix-only.shs` (fatal
  `--selftest`, 3 fixtures) fails on `app.io.*`, `std.nogc_sync_mut.io.*`,
  `io_runtime`, SFFI imports, `extern fn`, `@rt`, or `rt_*(` calls in the client.
  Verified FAIL on the pre-fix content, PASS after.

## Remaining (not in client scope, filed here)

Controller side (`src/app/orchestrator`, which imports the client's decode fns):
- `src/app/orchestrator/main.spl:2` — `use std.sffi.cli_args.cli_get_args` (raw SFFI).
- `src/app/orchestrator/caret_session_protocol_v1.spl:11` — `use std.nogc_sync_mut.package_sffi.{set_permissions}`.

Std below the client's closure: `src/lib/nogc_sync_mut/orchestration/host_execution_observation_v2.spl:11-13`
imports `io.file_ops`, `io_runtime.dir_create` and `sffi.fs.file_atomic_write_mode`;
the client only calls its pure `host_execution_observation_decode_v2`.
