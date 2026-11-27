# bin/caret ignores CARET_ENTRY, so the bin/cs source fallback runs the wrong entry

- **Date:** 2026-11-14
- **Severity:** P3
- **Status:** fix-implemented-verification-pending

## Symptom

`bin/cs` exports `CARET_ENTRY=src/app/llm_caret/cs_main.spl` and delegates to `bin/caret`.
In source-fallback mode (`SIMPLE_CARET_ALLOW_SOURCE_FALLBACK=1`) `bin/caret` hardcoded
`src/app/llm_caret/main.spl`, so `cs` launched the caret CLI instead of the dashboard.
`bin/cs.cmd` does not go through `bin/caret`, so there is no Windows gap.

## Fix

`bin/caret` uses `CARET_ENTRY` when set (relative paths resolve against the repo root). It must
be an existing file under `src/app/llm_caret/` with no `..` segment; otherwise it exits 127 with
an error. Unset keeps the old default. Spec: `test/00_unit/scripts/caret_launcher_entry_spec.shs`
(red on the old launcher, 6/6 green after).
