# Stage4 CLI run raw-output owner

**Status:** OPEN (unverified 2026-09-12)

## Reproduction

Stage4 HIR lowering stopped in
`src/app/io/_CliCommands/run_commands.spl` with unresolved `print_raw`.

## Fix

`cli_ops.spl`, the existing owner of the adjacent `_cli_eprint` adapter, now
owns `_cli_print_raw` and its runtime declaration. Run-command stdout routes
through that explicit module import instead of relying on an undeclared global
builtin name.

## Regression evidence

`cli_run_output_owner_spec.spl` locks the stdout route and the adjacent stderr
adapter ownership.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
