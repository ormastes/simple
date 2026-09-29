# Duplicate-check report path silently did nothing — 2026-07-23
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED IN SOURCE / FRESH CLI EVIDENCE PENDING

`report-path` was parsed but no canonical CLI path called the existing SDN
writer. `--format sdn` now writes exactly one lexical report at that path and
returns nonzero when the write fails.

The focused contract covers report creation and an unwritable child path.

