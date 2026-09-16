# domain_arena v1/v2 API surface mismatch
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected specs (left RED)
- test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl
  (write_byte / DOMAIN_ARENA_V1_MAX_QUOTA_BYTES removed from src)
- test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v2_spec.spl
  (module std.nogc_sync_mut.mission_critical.domain_arena_v2 does not exist;
  only v1 is present after fixing the spec's missing `std.` import prefix)

## Unblock condition
Either restore the v1 write_byte/quota API and the v2 module, or port both
specs to the current arena API with a reviewed mapping.

