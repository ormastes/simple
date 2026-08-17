# `_cli_driver_binary()` seed-sibling lookup fails under symlinked argv0

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-07-11 · **Status:** worker-side workaround landed in check_entry.spl; durable
fix landed in working copy (src/app/io/cli_ops.spl), pending next stage-4 rebuild + redeploy

## Symptom

Any invocation of the deployed stage-4 CLI **through the `bin/simple` symlink** silently
loses `run`/`-c` delegation to the seed sibling and falls into the slow in-process compiled
frontend. Measured: `bin/simple run src/app/check/main.spl <file>` times out at 60s+ with
self-hosted `[parser_error]` floods, while the identical command via the real path
`bin/release/aarch64-apple-darwin/simple run ...` delegates to `simple_seed` and completes
in ~3s. This made the whole `check` chain (stage-4 → seed → check_entry worker) look hung
(worker killed by check_entry's 300s timeout, zero output upstream).

## Root cause

`_cli_driver_binary()` → `_cli_seed_sibling_path()` derives the sibling from
`_cli_current_exe_path()`, which is argv0-based (`src/app/io/cli_ops.spl:125`). With
argv0 = `bin/simple` (symlink), the derived sibling is the nonexistent `bin/simple_seed`,
the lookup fails, and delegation is skipped without any diagnostic.

## Fix

- Landed workaround: `resolve_worker_binary()` in `src/app/cli/check_entry.spl` spawns the
  worker via the resolved `bin/release/<triple>/simple` path (fallback `bin/simple`);
  check chain 300s+ → 2.9s. Effective immediately because check_entry.spl is interpreted
  fresh by the seed on every `check`.
- Durable fix (this bug): `_cli_current_exe_path()` / `_cli_seed_sibling_path()` must
  resolve symlinks (realpath on argv0, or /proc/self/exe-equivalent via
  `_NSGetExecutablePath` on macOS) before deriving the sibling. Lives in the compiled
  stage-4 binary, so it only takes effect after the next stage-4 rebuild + redeploy.
  While fixing, add a one-line stderr note when a would-be delegation is skipped because
  the sibling is missing — the silent fallback is what made this expensive to find.
  **Landed 2026-07-11** in `src/app/io/cli_ops.spl`: new private helper
  `_cli_resolve_symlink(path)` wraps the existing `rt_path_absolute` extern (already
  declared in `src/lib/nogc_sync_mut/ffi/io.spl`, implemented in
  `src/compiler_rust/runtime/src/value/sffi/file_io/path.rs::rt_path_absolute` via
  `std::fs::canonicalize`, which resolves symlinks — including multi-hop chains — in one
  call and falls back to a cwd-joined absolute path on failure/nonexistent input, never
  empty). `_cli_current_exe_path()` now returns `_cli_resolve_symlink(_cli_resolve_argv0(...))`
  instead of the raw unresolved argv0. No new Rust extern was needed — `rt_path_absolute`
  already existed and takes a single scalar `text` arg, so it is unaffected by the
  `rt_process_run` args-array JIT marshalling bug documented earlier in the same file
  (`cli_ops.spl:72-74`), which is why a shell-out (`readlink -f` via `_cli_shell`) was
  deliberately avoided. Verified: `rt_path_absolute("bin/simple")` resolves to
  `bin/release/aarch64-apple-darwin/simple` (the real seed-sibling directory) via a
  standalone probe run under the Rust seed. `_cli_driver_binary()` also now `eprint`s
  `"simple: seed sibling not found, skipping delegation: <path>"` when the resolved
  sibling path doesn't exist, per the visibility ask above. Net +15 lines in
  `src/app/io/cli_ops.spl`. Takes effect after the next stage-4 rebuild + redeploy since
  this is compiled-binary code; left uncommitted per task scope.

## 2026-08-17 reproduction attempt (CLI lane)

Classified by CONTENT. `src/app/io/cli_ops.spl` no longer resolves the driver
from argv0 first: `_cli_current_exe_path()` (line 158-188) canonicalizes
`/proc/self/exe` IN-PROCESS via `rt_path_absolute` (`_cli_resolve_symlink`,
line 146-156) and only falls back to `sys_get_args()[0]` + `_cli_resolve_argv0`
+ `_cli_find_on_path` when that yields nothing or on Windows. The symlink case
this bug is about (`bin/simple` -> `bin/release/<triple>/simple`) is therefore
answered by the kernel, not by argv0. `_cli_is_current_exe` (205) additionally
resolves the CANDIDATE's symlinks, the specific regression called out in the
in-source comment at line 213-217.

Repro spec run: `test/01_unit/app/io/cli_argv0_resolution_spec.spl` — see the
`Results:` line recorded alongside this entry.
