# Slang JIT physical prefill reports no memory slot, then SIGBUS

Date: 2026-09-09
Status: open; blocks Simple-owner benchmark qualification

## Reproducer boundary

After the full-width signed SFFI result fix in PR #519, the diagnostic Rust
driver runs `test/fixtures/slang_paged_kv_provider/owner_smoke.spl` through the
real external provider and reaches:

```text
OWNER_STAGE execution_namespace_ready
OWNER_STAGE activate
OWNER_STAGE cold_generate
decode: failed to find a memory slot for batch of size 1
SIGBUS
```

This is later than the former `rt_value_raw_i64` abort and therefore a distinct
failure. The session stopped after its third owner-smoke verify/fix cycle.

## Exclusions

- The identical model and provider pass prefill, boundary, and decode numerical
  parity through the native C gate.
- A provider-only control also passes with the owner's 128-token request limit,
  four-token pages, and 64-page cache capacity.
- Separating configured sequence context from total page capacity did not
  change llama's rounded internal context and did not explain the failure; that
  experiment was reverted.
- The provider emits the memory-slot diagnostic only after pool activation and
  immediately after the Simple owner enters cold generation.

These controls localize the remaining fault to the Simple JIT/WFFI-driven
physical prefill path or its failure cleanup, rather than model compatibility,
provider tensor parity, or cache-capacity sizing.

## Required next diagnosis

- Capture the exact arguments and return statuses for request tokenization,
  table begin/push, page prefill, commit, and abort without rerunning the broad
  owner smoke first.
- Compare those values with the passing C control, especially request, pool,
  transaction, page handles, token count, and writable rows.
- Add a bounded WFFI fixture that exercises the cold transaction call sequence
  and fails before entering llama when an argument differs.
- Fix the generic JIT/WFFI transport or provider cleanup owner; do not special
  case the benchmark prompt and do not weaken provider failure handling.
- Resume owner-smoke qualification in a fresh scoped session, then produce the
  five-pair snapshot/physical benchmark evidence.
