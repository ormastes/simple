# Stage4 CLI run raw-output owner

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
