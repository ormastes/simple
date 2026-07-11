# `_cli_driver_binary()` seed-sibling lookup fails under symlinked argv0

**Date:** 2026-07-11 · **Status:** open (worker-side workaround landed in check_entry.spl;
durable fix needs a stage-4 rebuild)

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
