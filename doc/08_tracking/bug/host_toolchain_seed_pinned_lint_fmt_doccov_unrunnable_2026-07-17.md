# Host toolchain seed-pinned: lint/fmt/doc-coverage (and .spl-only CLI surface) unrunnable

**Date:** 2026-07-17
**Severity:** high (three tooling lanes dead on the host; masked by the seed-stopgap deploy)
**Status:** open

## Symptom

With `bin/simple` currently a Rust-seed stopgap (deployed 2026-07-11) and the
fresh seeds at `src/compiler_rust/target/{release,bootstrap}/simple` (2026-07-17):

- `bin/simple lint <file>` / `bin/simple fmt --check <file>` (deployed): dies with
  `error: semantic: unknown extern function: rt_cli_arg_count` — the Jul-11
  binary's extern allowlist predates the scalar CLI-arg externs (7714fcb2783).
- `<fresh seed> lint|fmt`: fails closed with
  `error: rt_cli_run_lint is not supported in interpreter mode` /
  `rt_cli_run_fmt ...` — these subcommands require the native-compiled CLI.
- `<any seed> doc-coverage`: `error: file not found: doc-coverage` + usage dump,
  exit 1. The seed front-end treats subcommands it does not know as script
  paths, so the pure-Simple dispatch handler
  (`src/app/cli/_CliMain/main_and_help.spl:270 run_doc_coverage`) is never
  reached. The same applies to the whole .spl-only subcommand family when the
  active binary is a seed.
- `simple check <file>` works (exit 0) on the fresh seed — the pure-Simple
  check path is healthy.

## Root cause

Not a defect in the .spl tooling itself: the host has no current true
self-hosted `bin/release/<triple>/simple`. The known whole-compiler redeploy
wall (#99 family; see
`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`)
means lanes that need either (a) a fresh extern allowlist or (b) native CLI
hooks (`rt_cli_run_lint`/`rt_cli_run_fmt`) or (c) the .spl CLI as the real
entrypoint are all pinned to a stale/incapable binary.

## Fix direction

1. Strategic (in progress 2026-07-17): dynSMF toolchain entries
   (`lint_tool`, `fmt_tool`, `fix_tool`, `todo_scan`, `mcp_diag_tools`) so
   tool updates load as small precompiled modules instead of requiring the
   whole-compiler redeploy.
2. Tactical: refresh the deployed stopgap from the current seed build
   (cp to `.new` + `mv`) so at least the extern-allowlist class of failures
   (lint/fmt on deployed) moves to the interpreter-mode class until the true
   self-hosted redeploy lands.
3. The self-hosted redeploy itself remains the real fix (do not race it; see
   memory/#99).

## How found

Tooling-surface smoke matrix (check / sdoctest / md / doc / test / compile /
run) during the 2026-07-17 test-runner hardening campaign.
