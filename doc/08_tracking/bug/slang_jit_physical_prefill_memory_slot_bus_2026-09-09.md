# Slang JIT physical prefill reports no memory slot, then SIGBUS

Date: 2026-09-09
Status: decode-position and cleanup-dispatch corruption fixed in source;
physical generation passes, shutdown telemetry reset remains unqualified

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
decode transaction. That call exposed cursor `8`, submitted position `48`, and
transaction end `9`; the expected values were `6`, `6`, and `7`. The submitted
position is a tagged-small-integer artifact (`48 == 6 << 3`).

Two generic compiler defects caused this transport corruption. Scalar
enum-pattern bindings carried a concrete `HirStmt::Let` type but left the
authoritative local slot as `Any`, allowing MIR to re-box extracted values. A
return-only error arm also contributed its return-expression type to a match
value join, degrading the successful scalar arm to `Any`; arithmetic then
inserted `BoxInt` immediately before the raw-i64 `_decode_one` call.

The binder now patches its local slot and match joins ignore arms that
definitely return. Focused HIR regressions cover both cases. After rebuilding
the driver, GDB proves transaction `3` now reaches llama with cursor `6`,
position `6`, and end `7`; all visible admission predicates pass.

Generation completes transactions `2` through `6` with the correct resolved
commit/decode/abort entry points. The subsequent request cleanup crosses
`_call1` with `37` in the function-pointer position. `37` is the first
generation-safe native request handle (`SLANG_REQUEST_MAX_ENTRIES + 1`), proving
the function-pointer position is overwritten with the second source argument
before `spl_wffi_call_i64`; the observed shape is consistent with transposition.
The provider pointer stored in `GgmlBackend` remains intact. The wrappers now
separate the capability branch and snapshot both scalar arguments before the
helper call. This source repair awaits a fresh owner-smoke cycle.

## Required next diagnosis

- In a fresh verification session, prove close/cancel receive the resolved
  function pointer first and the request handle second, then complete cold,
  exact-repeat, and prefix-extension generation.
- Produce the
  five-pair snapshot/physical benchmark evidence.
### 2026-09-09 cleanup-boundary follow-up

The post-repair owner smoke still reaches `cold_generate` and terminates with
SIGBUS (`rc=135`). GDB again stops at address `0x25`; `spl_wffi_call_i64`
receives `[Int(37), Array(...), Int(1)]`, with `fptr=37`. This proves the shared
`_call1(fptr, a0)` cleanup invocation transposes its scalar parameters after the
physical decode sequence. Request handle 37 is therefore called as an address.

The next candidate keeps request close/cancel at lexical WFFI boundaries instead
of passing their function pointer and handle through `_call1`. It requires a
fresh owner-smoke run in the next bounded verification cycle before benchmark
evidence is admissible.

### 2026-09-09 unique cleanup ownership result

A rebuilt branch-local compiler plus temporary stage probes showed that cold
prefill and all four sample/piece/decode iterations completed. Cleanup invoked
the backend close correctly first, with the resolved provider address and
native handle `9`. The following logical `PAGED_MANAGER.close_request(...)`
was incorrectly dispatched to the unrelated backend free function of the same
name, producing `f_request_close=37` and a garbage request handle.

The backend functions are now uniquely named `close_backend_request` and
`cancel_backend_request`. With that collision removed, cold generation,
exact-repeat reuse, prefix extension, and provider shutdown all complete
without SIGBUS. The remaining owner-smoke failure is narrower: post-shutdown
state reports `active=false` and `pool=0`, while the optional telemetry query is
still observed as non-nil. This must be resolved before benchmark admission.
