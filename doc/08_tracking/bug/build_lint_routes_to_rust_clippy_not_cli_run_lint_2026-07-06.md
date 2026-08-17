# `bin/simple build lint` routes to Rust-driver clippy — pure-Simple `cli_run_lint` never executes

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## 2026-08-17 verification (CLI lane) — STILL OPEN, confirmed by source content

Root cause confirmed unchanged in current source:

- `src/compiler_rust/driver/src/cli/commands/misc_commands.rs:130`
  `"lint" => handle_build_lint_with_args(&sub_args[1..])`.
- `handle_build_lint_with_args` (same file, ~line 185-200) ignores every
  positional argument except `--fix` and unconditionally runs
  `cargo clippy --manifest-path src/compiler_rust/Cargo.toml --workspace -- -W clippy::all`.
  A `.spl` path passed to `bin/simple build lint <file>` is silently discarded.
- The build help text at line 141 documents this as
  `"lint           Run clippy linter on Rust workspace"`, so the routing is
  deliberate, not a dispatch slip; the defect is that it shadows the
  pure-Simple linter under a name users reach for.
- The pure-Simple linter is alive and reachable by the OTHER spelling:
  `src/app/cli/_CliMain/main_and_help.spl:349` (`elif str_eq(first, "lint")`)
  routes to `cli_run_lint` in
  `src/app/io/_CliCommands/run_commands.spl:225`, which loops over file
  arguments and calls `run_lint_file` (line 323). So
  `bin/simple lint <file>` works; `bin/simple build lint <file>` does not.

Not patched by this lane: the fix belongs in `misc_commands.rs`, which this
lane was explicitly scoped OUT of editing (Rust seed, other lane's file).
Recommended fix, for whoever owns it: in `handle_build_lint_with_args`, when
any non-flag argument is present (or any argument ends in `.spl`), delegate to
the pure-Simple `lint` command instead of invoking cargo clippy.
