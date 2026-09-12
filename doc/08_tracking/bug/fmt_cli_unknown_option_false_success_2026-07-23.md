# fmt CLI unknown options could succeed
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
