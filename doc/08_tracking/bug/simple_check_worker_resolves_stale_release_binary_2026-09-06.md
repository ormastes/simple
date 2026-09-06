# `simple check` resolves its worker to a stale release binary and fails on every target

- date: 2026-09-06
- status: MITIGATED (root cause still open — needs a redeploy)
- area: app/cli, tooling

## Symptom

On this macOS checkout, EVERY `bin/simple check <anything>` failed:

    $ bin/simple check src/app/editor/
    error: compile failed: parse: in ".../src/app/check/main.spl":
           Unexpected token: expected expression, found Colon
    (exit 1)

The named file is not a target the user asked to check — it is `check`'s own
worker entry. The same error appears for a nonexistent target, which is the tell:
the failure happens before any target file is looked at.

## Root cause

`src/app/cli/check_entry.spl` spawns a worker `<binary> run src/app/check/main.spl
<files>`. `resolve_worker_binary()` (:36-64) prefers `bin/release/<triple>/simple`
purely for delegation speed, and adopts it on `file_exists` alone. Here that path
is `bin/release/aarch64-apple-darwin/simple`, dated **2026-07-25**, which cannot
parse current tree source — so it dies loading the worker entry and `check`
reports a parse error the user cannot act on.

The worker entry is interpreted from SOURCE every run, so any deployed binary
older than the tree can fail this way. `file_exists` is not evidence that a
binary can run the code it is about to be handed.

## Fix applied (mitigation)

`src/app/cli/check_entry.spl`: `worker_entry_load_failed(stderr)` recognises the
worker's own load failure (stderr carries `compile failed` AND names
`CHECK_WORKER_ENTRY`), and `run_worker()` retries once on `bin/simple` — the
binary that dispatched us, which by construction can load the entry. The retry
prints a diagnostic naming the binary that failed, so the stale deploy stays
visible instead of being silently papered over. Zero cost on the happy path.

Target-file findings are reported by the checker as `<path>: <error>` on stdout,
so they never match the stderr signature and never trigger a retry.

## Root cause NOT fixed

`bin/release/aarch64-apple-darwin/simple` is still a 2026-07-25 binary that
cannot parse the current tree. The real repair is a redeploy, which requires a
bootstrap and is out of scope for the lane that found this.

## Specs

- Reproducing (system): `test/03_system/plan_acceptance/editor_markdown_editing_subsystem_spec.spl`
  `# @req REQ-EDITOR-MD-008` — `bin/simple check src/app/editor/` must exit 0.
  Measured 1 of 9 failing before the fix, 0 of 9 after.
- Generalization (unit): `test/01_unit/app/cli/check_entry_worker_load_failure_spec.spl`
  — `worker_entry_load_failed` must fire on a worker-entry load failure and must
  NOT fire on a target-file diagnostic or on empty stderr.

## Planted control

`worker_entry_load_failed` body forced to `false` ->
`bin/simple check src/app/editor/commands.spl` exits 1 with the parse error;
restored -> `All checks passed (1 file(s))`.
