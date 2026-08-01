# Simple lint silently accepted unknown options — 2026-07-23

**Status:** SOURCE FIXED / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

`simple lint test/fixtures/lint/clean.spl --bogus`, bare `--profile`, and empty
`--profile=` continued into normal linting. A clean file could therefore exit 0
even though the invocation was invalid.

## Root cause and fix

The public wrapper collected known wrapper flags and file paths but ignored all
other dash-prefixed arguments. The compiler lint owner only inspected flags it
understood, so neither layer rejected the typo.

The wrapper now validates its closed supported option set before file work and
returns usage exit 2 with human or JSON error output. The focused contract
covers unknown, bare-profile, empty-profile, and JSON unknown-option cases.

A fresh pure-Simple Stage 4 CLI must run the focused contract and public lint
smoke before qualification.
