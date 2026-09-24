# Enterprise vertical modules deleted from src
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected specs (left RED)
- test/01_unit/lib/nogc_sync_mut/enterprise_expense_spec.spl
- test/01_unit/lib/nogc_sync_mut/enterprise_quality_spec.spl
- test/01_unit/lib/nogc_sync_mut/enterprise_assets_spec.spl
- test/01_unit/lib/nogc_sync_mut/enterprise_warehouse_spec.spl

## Observed
`cannot resolve import` / `module path segment not found`: the modules
`enterprise_expense`, `enterprise_quality`, `enterprise_assets`,
`enterprise_warehouse` no longer exist under src/lib/nogc_sync_mut/. The
specs' entry points (e.g. `expense_setup`) were not moved to
enterprise_finance/inventory either.

## Unblock condition
Reinstate the modules (or port the specs to the replacement modules with a
reviewed mapping). Verify with `bin/simple run` on each spec.

