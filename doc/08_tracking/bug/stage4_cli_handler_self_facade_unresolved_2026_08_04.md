# Stage 4 CLI handler self-facade leaves callables unresolved

## Status

Fixed in the LLVM 23.1 Stage 4 bootstrap lane on 2026-08-04.

## Symptom

After the CLI-lint owner repair, the next full Stage 4 cycle parsed all 1,351
surfaces and completed HIR traversal, then reported unresolved `check_file` and
`cli_compile` in `src/app/io/_CliCommands/handler_commands.spl`.

## Root cause

`handler_commands` used `app.io.cli_commands.*`. That compatibility facade
re-exported both `run_commands` and `handler_commands`, so the consumer imported
itself and relied on sibling names arriving through a cyclic wildcard. Stage 4
did not invent physical callable owners for the two unresolved names.

## Fix and regression

The handler now imports `cli_not_implemented` and `cli_run_file` from the
physical run-command sibling, `cli_compile` from its compile implementation,
and `check_file` plus `CompileResult` from their driver owners. Four unused
formatter/fix/lint imports are removed. The focused native handler contract
imports the physical handler module and executes its bounded web-handler path.
