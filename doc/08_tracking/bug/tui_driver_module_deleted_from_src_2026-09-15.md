# TuiDriver removed from nogc_sync_mut/ui_test
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/ui_test/tui_driver_spec.spl

## Observed
`TuiDriver` is not defined anywhere in src/; the ui_test tui_driver module
is gone. Import fails at module resolution.

## Unblock condition
Restore TuiDriver (or land its successor and port the spec deliberately).

