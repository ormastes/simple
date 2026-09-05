# BUG: native-build ignored unknown options

## Reproduction

Append `--entry-clousre` to an otherwise valid pure-Simple `native-build`
command. Before the fix, the parser ignored it and could publish a binary with
exit 0 instead of rejecting the misspelling.

## Root cause

`cli_native_build` decoded known flags but had no closed fallback for a token
starting with `-`.

## Fix and regression

`cli_native_build_option_error` validates supported forms and required values
before compilation. `test/01_unit/app/compile/cli_native_build_spec.spl`
checks unknown, option-looking missing values, and invalid worker counts
without invoking the compiler.

## Policy

A sole help flag exits 0. Any malformed argument list, including one that also
contains help, exits 2 before the worker or output staging is reached.
