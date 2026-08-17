# Essential-tools smoke silently ignores artifact argument

- **ID:** `essential_tools_smoke_ignored_artifact_argument_2026-08-02`
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** Critical (wrong-binary verification)

## Reproduction

`sh scripts/check/check-bootstrap-essential-tools-smoke.shs /fresh/stage4`
previously ignored `/fresh/stage4` and tested `bin/simple` unless the caller also
set `SIMPLE_BINARY`. That could certify a stale deployed binary instead of the
fresh candidate.

## Fix

The script now accepts zero or one positional artifact, rejects extra arguments,
and rejects a conflicting positional path plus `SIMPLE_BINARY`. Existing
environment-only bootstrap invocation remains supported.

