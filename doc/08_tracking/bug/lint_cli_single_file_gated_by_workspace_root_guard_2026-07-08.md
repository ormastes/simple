# Bug: single-file `simple lint <file>` exit code is gated by the workspace-root guard + `bin/simple <unknown>` exits 0

- **ID:** lint_cli_single_file_gated_by_workspace_root_guard_2026-07-08
- **Severity:** P3 (tooling UX / test-determinism). Two related findings in the refactored
  lint/fmt/fix CLI surface. Neither corrupts output; both make behavior surprising and make
  `test/03_system/feature/app/code_quality_tools_spec.spl` unable to assert a deterministic
  "clean file lints OK, exit 0".
- **Area:** `src/app/io/cli_lint_commands.spl` (`cli_run_lint` `:33` root-guard call),
  `src/app/cli/lint_entry.spl` (help-on-bare-command), the `bin/simple` top-level dispatcher.
- **Status:** OPEN — found 2026-07-08 while updating stale #38 assertions in
  `code_quality_tools_spec.spl`.

## Finding 1 — single-file lint gated by workspace-root guard

`cli_run_lint` runs `_cli_run_workspace_root_guard()` (`cli_lint_commands.spl:33`) unconditionally,
before/independent of the per-file lint. When the guard finds ANY workspace-root violation (e.g. the
`export use *` warnings currently present in `src/app/io/cli_commands.spl`), it forces `exit_code = 1`
for the WHOLE invocation — even `simple lint /tmp/clean_fixture.spl`, where the fixture lives outside
the repo and is itself clean.

Consequence: a user (or CI) linting a single clean file cannot get exit 0 while the repo has any
root-guard violation, and the emitted diagnostics are dominated by repo-wide / module-graph findings
unrelated to the target file. This makes `simple lint <file>` unusable as a focused single-file check
and makes deterministic per-file test assertions impossible.

**Fix direction:** decouple the workspace-root guard from single-file `lint <file>` runs — run the
guard only for the no-argument / whole-workspace lint mode, or report its result separately without
folding it into the per-file exit code.

## Finding 2 — `bin/simple <unknown-command>` exits 0

`bin/simple totallyboguscmd` prints `error: file not found: totallyboguscmd` and exits **0** — the
dispatcher treats an unrecognized first token as a filename to run, and a missing file is not an
error exit. So an unknown command (or a typo) silently "succeeds". There is no unknown-command
rejection at the dispatcher layer (confirmed: `command_dispatch_spec.spl` has no such case).

Note: the thin `lint_entry.spl` never receives unknown commands in production (the dispatcher routes
only `lint`/`fmt`/`fix` to it), and the heavy `lint_worker.spl` DOES still reject an unknown command
with exit 1 when it receives one with a file arg (`Unknown command: <cmd>`), so the retargeted
`code_quality_tools_spec` "unknown command" case exercises the worker's real rejection.

**Fix direction:** the top-level dispatcher should exit non-zero on `file not found` for a bare token
that is neither a known subcommand nor an existing file.

## Finding 3 — real linting is unavailable under `bin/simple run` (interpreter mode)

Driving lint through the entrypoint in interpreter mode (`bin/simple run src/app/cli/lint_entry.spl
lint <file>` → `lint_worker.spl` → `cli_run_lint`) fails with
`error: rt_cli_run_lint is not supported in interpreter mode` and exits 1 — the real lint pass is a
native runtime function only present in the compiled `bin/simple`. So a spec that exercises linting
via `bin/simple run` can only cover the pure-Simple help/dispatch/rejection paths, never a real lint
result; real linting must go through the compiled `bin/simple lint` subcommand.

This is why `code_quality_tools_spec.spl` was updated (2026-07-08, #38) to assert the deterministic
interpreter-mode failure for a file lint rather than a "clean file → exit 0 + OK" outcome. It fails
closed (explicit message, non-zero exit) rather than silently, which is acceptable — but ideally the
spec (or a companion) should drive the compiled `bin/simple lint` to cover real lint behavior.
