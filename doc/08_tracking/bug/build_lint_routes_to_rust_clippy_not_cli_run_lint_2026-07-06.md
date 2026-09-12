# `bin/simple build lint` routes to Rust-driver clippy — pure-Simple `cli_run_lint` never executes
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- Date: 2026-07-06
- Severity: medium (policy violation + inert lint-time gates)
- Found during: backend-isolation gate wiring verification (task #22, integration round 3)

## Symptom
`bin/simple build lint <file>` does not execute the pure-Simple lint path
(`src/app/io/_CliCommands/run_commands.spl` `cli_run_lint`). Both the deployed self-hosted
binary and the seed route `build lint` through the Rust driver's `handle_build`, which
intercepts the "lint" subcommand and runs **`cargo clippy` on the Rust workspace** instead:
`src/compiler_rust/driver/src/cli/commands/misc_commands.rs:126,181`.

## Consequences
1. Violates the repo rule "Default tooling = pure-Simple self-hosted binary, not the Rust
   seed" (CLAUDE.md) — the user-facing lint command is a Rust-workspace clippy run.
2. Any gate wired into `cli_run_lint` is **inert on the `build lint` lane**: the
   workspace-root guard and the new ui-backend-isolation gate
   (`scripts/check/check-ui-backend-isolation.shs`, wired 2026-07-06 in commit 4cf42eb41d)
   only fire on lanes that actually execute `cli_run_lint`.
3. Current effective enforcement of the isolation ratchet is the pre-commit hook
   (`scripts/hooks/pre-commit` runs the gate script directly — verified working) plus direct
   script invocation.

## Evidence
- Interpreted source-lane A/B (temp driver calling `cli_run_lint`): `ui_backend_isolation_*`
  lines appear, root guard runs, output otherwise byte-identical — the wiring is correct.
- Deployed lane: `bin/simple build lint` output contains no `cli_run_lint`-side output at
  all; exit unchanged pre/post wiring (0→0).

## Fix direction
Retire the Rust-driver "lint" interception (or make `handle_build` delegate `lint` to the
self-hosted `cli_run_lint` lane), per the default-tooling rule. Related: the stage-4
compiled-frontend/redeploy work (doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md,
task #21) — the same delegation lane is involved.

## Workaround (current)
Pre-commit hook enforcement + `sh scripts/check/check-ui-backend-isolation.shs` directly.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
