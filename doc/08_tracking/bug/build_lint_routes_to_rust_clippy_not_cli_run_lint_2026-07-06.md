# `bin/simple build lint` routes to Rust-driver clippy — pure-Simple `cli_run_lint` never executes
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Closed 2026-11-25 (p2w1-ah lane) — stale; duplicate of the PR #11522 resolution

Same root cause and same resolution as
`build_lint_subcommand_triggers_full_driver_rebuild_2026-06-15.md`, resolved
2026-11-25 by PR #11522 (merge eec4a8db17f): the `build lint` -> cargo
clippy hijack lives only in the Rust seed (`handle_build` /
`handle_build_lint_with_args` in
`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`, reached because
the seed's Simple-first `build` dispatch is dead), while the pure-Simple
self-hosted CLI already routes correctly — `src/app/build/cli_entry.spl:179-180`
dispatches `lint` to `cli_run_lint(args[1:])` (confirmed by source inspection
on release/1.0.0 @ 602063b765f). Per repo policy the seed is bootstrap-only,
so the residual seed-side interception is out of scope for a pure-Simple fix;
the concrete seed fix is recorded in the sibling doc. The inert-gate
consequence noted here (the ui-backend-isolation gate wired into
`cli_run_lint`) does not apply on the self-hosted lane, which does execute
`cli_run_lint`. Execution re-verification on this host is environment-blocked
(the pinned seed rejects the `@representation_boundary` annotations at HEAD
repo-wide); closure rests on the PR #11522 evidence plus current source
inspection. Status: CLOSED (stale / duplicate of PR #11522).
