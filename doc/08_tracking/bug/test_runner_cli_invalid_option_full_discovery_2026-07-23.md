# Test runner invalid options fell back to full discovery — 2026-07-23

**Status:** SOURCE FIXED / FOCUSED BOOTSTRAP CONTRACT PASS / PURE-SIMPLE QUALIFICATION PENDING

## Reproduction

`simple test --unknown` and `simple test --tag` were silently ignored by the
argument parser, which selected the default `test/` root and could start a full
discovery run.

## Root cause and fix

The parser intentionally has a stable `TestOptions` return type, so it could
not communicate invalid usage. A shared preflight now recognizes every parser
flag/form, preserves signed split values, and returns usage status 2 before
configuration or discovery. Run-management commands retain their existing
early dispatch.

The focused contract covers unknown and bare options, option tokens swallowed
as values, empty split/equals values, signed `--timeout -1`, and a valid value
ending in `=`.
