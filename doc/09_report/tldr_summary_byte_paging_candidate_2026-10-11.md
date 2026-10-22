# TLDR summary byte paging candidate — 2026-10-11

Status: **applied locally on `release_phase3`; executable tests unrun; performance
unmeasured**. This is a source-reviewed candidate, not Phase3 admission or a
release/performance PASS. No closed baseline attempt was reopened and no fourth
compiler build was started for this review.

## Change and invariants

`src/compiler/80.driver/cache/summary/summary_store_v1.spl` now reads rendered
byte length directly for stat and copies only the requested byte range for
partial reads/pages. A complete range (`start == 0 && end == rendered.len()`)
uses the existing bulk `text_to_bytes` conversion, returning fresh bytes.
Partial ranges begin with `text_to_bytes("")` to retain packed storage instead
of the tagged-slot representation used by an empty array literal.

Bounds are validated before computing `start + min(size - start, limit)`.
For accepted requests, `0 <= start <= end <= size`, so addition cannot overflow.
Selected bytes, page conversion via `bytes_to_text`, completion, token bindings,
page digests, and independent returned arrays retain their prior meanings.
UTF-8 sequences may still be split at byte boundaries, using the existing
conversion policy. No schema, persistent format, or retained cache was added.

The original production file SHA-256 was
`08b123e61b103d8761d7a046eaf21a2fead4a044e8e44361fab7b8736bbcf044`.
The reviewed patch and historical candidate remain under
`build/native_probe/phase3-memory-perf-review-20261011/`.

## Allocation and push evidence

Source inspection establishes the following for the current native runtime:

- `runtime_native.c:8073` implements `rt_text_to_bytes` using
  `rt_byte_array_new_len`, whose constructor sets `RT_CORE_ARRAY_FLAG_BYTES`
  (`:7987`). Byte elements therefore occupy one byte.
- `runtime_native.c:8379` implements `rt_array_push` with an **i8 status** result,
  not a replacement array pointer. It reserves storage, then writes through
  `uint8_t*` when the packed flag is set.
- `runtime_native.c:8929` grows only the header's internal data buffer, selects
  element size from the existing flags, and preserves those flags. The outer
  array handle stays stable across reallocations.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:999` lowers
  array push to that i8-returning function, emits receiver writeback, and returns
  the original receiver as the language expression result. The array dispatch
  at `:3616` uses this helper. Standalone `bytes.push(...)` thus retains growth;
  assigning its result is unnecessary on this path.
- The alternate pure-Simple runtime's
  `src/runtime/simple_core/core_array.spl:679` also grows the internal items
  pointer and preserves the outer handle; its push at `:701` returns i8.
  This confirms handle stability, not packed-layout compatibility of that
  alternate runtime.

The reference interpreter also updates standalone local packed-byte pushes:
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:1685` handles
ByteArray identifier receivers, `:1782` pushes through `Arc::make_mut`, and
`:1864` returns the updated binding and method expression value. Statement
dispatch in `interpreter/block_exec.rs:326` and `interpreter/node_exec.rs:392`
consumes the binding update even when the expression value is discarded.
This is source inspection only; no Rust seed execution counts as qualification.
The separate legacy `src/app/interpreter/expr/calls.spl:175` still reports push
as unimplemented; reassignment cannot make that interpreter a qualified runner.

Consequently, partial-copy storage grows with requested bytes rather than the
entire rendering on the reviewed native path, with capacity rounding and array
headers. This is an algorithm/storage claim, **not a measured RSS improvement**.

## Remaining performance limits

`runtime_native.c:3647` indexes UTF-8 bytes directly but calls `strlen` per access
for raw pointers. Only the owned-string path has cached length. Publication's
renderer produces dynamic text through `lines.join("\n") + "\n"`
(`public_summary_projector.spl:227`); reopened stores still require qualification.

`SummaryStoreV1.row` continues to decode, hash, and re-render the whole summary.
The change removes an additional byte conversion after that validation; it does
not make the complete request O(page size). Small-page savings and throughput
improvements remain hypotheses until paired measurements exist.

## Regression and admission

`test/01_unit/compiler/cache/summary_store_byte_paging_spec.spl` exercises real
admitted store APIs against the old full-conversion-plus-slice oracle: UTF-8
2/3/4-byte scalars, every byte offset, limits 1/3/65/full, stat byte count,
read/page continuation, page digests, EOF, invalid bounds/cursors, mutation
isolation, and an owner-configured maximum-i64 limit. The 65-byte partial range
forces multiple capacity increases. Overflow is predicted to fail the old
addition-before-clamping implementation; no observed RED/GREEN result is claimed.

Before admission:

1. Qualify a pure-Simple runner exposing test/check/run; b580 lacks those public
   commands. Execute baseline then candidate regression once each and record
   actual failures/passes. Run existing `summary_store_v1_spec.spl` and
   `virtual_summary_registration_protocol_spec.spl` for consumer/auth parity.
2. Complete optimizer inspection, compiler/lib/MCP/LSP checks, and required
   core-runtime/MCP native smokes with the qualified runner.
3. Compare identical fixtures and immutable binary identities for tiny/full/EOF/
   maximum pages, ASCII/Unicode, in-memory/reopened stores, plus a raw-literal
   accessor control. Keep startup, warm, and build measurements separate.
4. Record p50/p95 time, peak/steady RSS, allocation telemetry, and exact payload/
   digest equality. Apply independent budgets and the optimization skill's joint
   time/memory gate. Missing evidence cannot be treated as a tradeoff pass.

Only patch application and whitespace checks have passed. Root owns local
integration and commit coordination; remote landing remains gated on Phase3 PASS.
