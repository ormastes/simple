# session CSRF compute_signature produces wrong HMAC-SHA256 output
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl
  (3 of 11 its fail)

## Observed
compute_signature returns `00000019000000b5...` (looks like leaked internal
bytes/handles) instead of the openssl HMAC-SHA256 oracle
`76e6d0e8d2475fc78a88f884145dd586abd43904408523306526b462f6b6934d`; the
same wrong bytes flow into csrf_token_for_session.

## Unblock condition
Fix the HMAC-SHA256 path used by the session signing module; the openssl
digests in the spec are ground truth.

