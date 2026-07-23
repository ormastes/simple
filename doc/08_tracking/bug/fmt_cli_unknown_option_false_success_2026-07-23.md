# fmt CLI unknown options could succeed

## Symptom

Both pure-Simple `fmt` owners ignored unrecognised dash-prefixed arguments, so
for example `simple fmt file.spl --bogus` could format or report success.

## Root cause and fix

The two command owners each parsed recognised flags and silently skipped all
other dash-prefixed arguments.  They now share `app.io.cli_fmt_options`, which
rejects every undocumented option before any file read, write, or formatter
output with exit status 2.

## Regression evidence

`test/01_unit/app/fmt_cli_option_validation_contract_check.spl` checks the
shared allowlist. The two isolated owner contracts check rejected invalid
options, accepted `--check`/`--write` forms against a missing path (no
mutation), and help's zero exit before file work. All three focused contracts
pass through the temporary bootstrap interpreter; pure-Simple/Stage 4 evidence
remains pending the fresh deployed runtime.
