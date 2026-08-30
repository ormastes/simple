# Examples-check invalid options could report false success — 2026-07-23

**Status:** SOURCE FIXED / FOCUSED BOOTSTRAP CONTRACT PASS / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

`simple examples-check examples --runx` silently ignored `--runx`, kept the
default compile mode, and could return success after compiling examples.
Bare, empty, or option-looking `--timeout`, `--limit`, `--binary`, and
`--report` values were also silently replaced by defaults. The entry help
incorrectly advertised an unsupported `--timeout-ms` spelling.

## Root cause and fix

The parser returned only a configuration object, so malformed flags had no
error channel. `examples_check_option_error` now validates the documented
forms before discovery and returns usage status 2 for unknown, missing, or
empty options. The focused contract covers the default-mode typo, missing and
option-token values, empty equals values, and documented valid forms.
