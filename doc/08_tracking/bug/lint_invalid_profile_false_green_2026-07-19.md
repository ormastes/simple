# Lint invalid profile false-green — 2026-07-19

**Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING

## Reproduction

`simple lint clean.spl --profile=relaible` silently ignored the misspelled
strictness tier and could report a clean result under the legacy policy.

## Root cause and fix

The shared lint entry called a configuration helper whose documented behavior
is to ignore unknown profile strings. Validate the CLI value with the existing
profile parser, emit a lint error, and return usage exit 2 before analysis.
The focused unit and essential-tools smoke retain the misspelled-profile case.
The new CLI rejection scenario passes under the temporary runner. A separate
pre-existing optional-profile assertion failure remains tracked independently.

`simple.sdn` `[lints]` parsing had the same fail-open behavior for unknown
profiles, unknown rule names, and invalid levels. The loader now preserves the
first validation error and `run_lint_file` returns usage exit 2 before analysis.
