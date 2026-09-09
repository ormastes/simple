# Slang JIT physical prefill reports no memory slot, then SIGBUS

Date: 2026-09-09
Status: SIGBUS cleanup cause isolated; provider rejection still under diagnosis

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

GDB proves that the signal is not raised inside llama: the bootstrap JIT calls
address `0x25` through `spl_wffi_call_i64` after prefill fails. The call has one
argument and corresponds to the provider transaction-abort edge. The expected
`GgmlBackend.f_page_table_abort` slot is field 64 at byte offset 512.

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
- A model-free symbol-integrity probe passes for field 64, and a post-activation
  probe proves the paged executor's stored backend still contains the exact
  `dlsym` address before generation.
- A generic 69-field record retains fields 63, 64, and 68 through a function
  parameter and optional global. Width alone is therefore not the defect.

These controls localize the SIGBUS to late aggregate-field projection on the
JIT/WFFI provider-error edge. Snapshotting the abort address in a scalar local
did not survive the failed foreign call either. The wrapper now returns the
operation error without a second WFFI dispatch; the request owner immediately
cancels the request, whose provider detach path aborts and clears every active
transaction. Pre-call validation still aborts directly.

A register-level breakpoint at `slang_ggml_page_prefill` proves the Simple
owner submits the expected arguments: transaction `2`, start position `0`,
token start `0`, and token count `6`. Inside llama, that batch has positions
`0..5`, one sequence ID `0`, one requested output at the tail, cursor `0`, and
transaction end `6`; every visible admission predicate passes.

Continuing from that breakpoint reaches `init_batch` a second time through
`slang_ggml_page_decode`, now with transaction `3`. Thus cold prefill succeeds;
the generic "batch of size 1" diagnostic belongs to the first generated-token
decode transaction. The remaining investigation is its cursor/end/table
invariant, not prompt tokenization or prefill capacity.

## Required next diagnosis

- Capture transaction `3` at the second `init_batch` call and identify its
  exact failed cursor/end/table predicate before changing provider behavior.
- Produce the
  five-pair snapshot/physical benchmark evidence.
