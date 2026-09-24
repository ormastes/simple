# Stage4 CLI run raw-output owner
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

