# Predicate-parser bootstrap gate ignores admitted Stage 4

Status: RESOLVED — `codex/session-01a023a8`

## Failure

The bootstrap completion owner exports the validated candidate as
`SIMPLE_BINARY` and `SIMPLE_BIN`, but
`check-predicate-parser-native-build.shs` selected only an explicit positional
argument, ambient `SIMPLE_STAGE2_BIN`, or `bin/simple`.

An isolated reproducer supplied distinct fake Stage 4 and ambient Stage 2
executables. With all three environment variables set, the checker invoked the
ambient Stage 2 fake and returned:

`selected=ambient-stage2 rc=1`

This permits stale or unrelated compiler evidence in an automated bootstrap
row after the exact Stage 4 candidate has already been admitted.

## Required fix

Preserve explicit positional override for direct Stage-2 diagnostics, then
prefer `SIMPLE_BINARY`, `SIMPLE_BIN`, legacy `SIMPLE_STAGE2_BIN`, and finally
the deployed default. Add a non-building resolver self-test covering exact
candidate priority and both compatibility fallbacks.

## Resolution

The checker now applies that priority order. Its non-building self-test covers
the explicit override, both exact-candidate names, the legacy Stage 2 fallback,
and the deployed default.
