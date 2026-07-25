# Bug: `simple run` stripped program flags that matched wrapper log options

**Status:** Fixed in source; fresh Stage 4 runtime qualification pending.

## Reproduction

`simple run fixture.spl --json` removed the program's `--json` argument.
`simple run fixture.spl -- --log-mode noisy` also let the wrapper parse the
program-only flag and could reject it before the entry file ran.

## Root cause and fix

`src/app/run/main.spl` parsed and removed shared log options from the complete
argument vector. It now consumes only the leading wrapper-option prefix and
preserves the file plus every following token, including `--`, unchanged.
Runtime flags before the file remain delegated while shared logging flags are
still collected; unsupported split `--surface VALUE` fails before delegation
instead of being silently consumed.
The prefix grammar mirrors the pure-Simple global parser plus the still-active
sandbox/resource flags of the delegated CLI, including `--lang VALUE`/`=` and
`--gc=off`, so those flags cannot make a later shared option look like a file.

## Regression evidence

`test/01_unit/app/run_cli_argument_boundary_contract_check.spl` covers a
leading wrapper option and post-file/`--` program flags.
