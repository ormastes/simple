# hal_clock_dispatch.spl deleted; time provider contract spec RED
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/io/rt_hal_time_provider_source_contract_spec.spl
  (3 of 4 its fail)

## Observed
src/lib/nogc_sync_mut/io/hal_clock_dispatch.spl no longer exists, and
time_ops.spl no longer carries the bounded critical provider contract tag
the spec greps for (`providers: pure+c+rust` block).

## Unblock condition
Restore hal_clock_dispatch.spl and the provider contract tag, or retire the
contract deliberately.

