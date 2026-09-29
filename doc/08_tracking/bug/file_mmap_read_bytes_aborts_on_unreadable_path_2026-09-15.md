# file_mmap_read_bytes aborts instead of returning Err
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/non_optional_nil_return_contract_spec.spl
  (11 of 12 pass; this one it stays RED)

## Observed
`file_mmap_read_bytes("/nonexistent/...")` should return Err (it is typed
`-> Result`), but raises `runtime: rt_file_mmap_read_bytes failed` and kills
the spec.

## Unblock condition
Make the wrapper catch the rt failure and return Err (see sibling
file_read_lines behavior), then re-run the spec.

