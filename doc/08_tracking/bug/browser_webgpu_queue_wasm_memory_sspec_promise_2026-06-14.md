# Browser WebGPU Queue WASM Memory SSpec Promise Harness Gap

Date: 2026-06-14
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
Priority: P2

## Summary

BrowserSession now implements a bounded software WebGPU device queue shape:
`navigator.gpu.requestAdapter()` returns an adapter with `requestDevice()`, and
the resolved device exposes `queue.writeBuffer(...)` with upload count, offset,
byte length, and checksum recording for `ArrayBuffer` and `Uint8Array` sources.

A direct BrowserSession probe verified a WASM instance can write bytes into
`i.exports.memory.buffer`, wrap that buffer in `Uint8Array`, and pass it to
`device.queue.writeBuffer(...)` with checksum `39` for bytes `12,13,14`.
However, the equivalent nested Promise chain as a standalone SSpec scenario
failed under the current SSpec harness without assertion detail, while the broad
`webgpu_js_wasm_simple_spec.spl` remains green.

## Expected

An executable SSpec should prove:

- `adapter.requestDevice()` resolves a software WebGPU device.
- `device.queue.writeBuffer(target, offset, new Uint8Array(i.exports.memory.buffer))`
  records offset `4`, byte length `65536`, checksum `39`, and bytes `12,13,14`.

## Current Evidence

- Runtime support exists in `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`.
- `webgpu_js_wasm_simple_spec.spl` proves `adapter.requestDevice` is exposed.
- Direct BrowserSession script probing produced `39:1:4:65536:39:12,13,14`.

## Follow-Up

Stabilize SSpec nested Promise handling or add a harness helper for settled
BrowserSession Promise drains, then add the queue-upload SSpec without weakening
the assertion or leaving the broad browser WebGPU spec red.

## Re-verification 2026-08-17 (UI/JS slice) — STILL OPEN, but MISCLASSIFIED

Classified by CONTENT. Runtime support is confirmed present in
`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` (the WebGPU/queue and
Uint8Array/`Symbol.iterator` machinery this scenario needs is live at
interpreter_native.spl:3901, 3942, 3972, 4388 and the Node-stream/async-iterator
definitions around 1791/2532).

**This is not a silent-wrong-result defect and does not belong in that triage
class.** This doc's own evidence says the runtime produced the CORRECT values
(`39:1:4:65536:39:12,13,14`) under a direct BrowserSession probe. The only thing
that fails is expressing that nested-Promise drain as an SSpec scenario. The
defect is in the *test harness's* Promise-settling support, not in any product
code path — no user-visible computation returns a wrong answer.

Nothing to fix in this slice's files; the fix is a `std.spec` harness helper for
settled BrowserSession Promise drains, per this doc's own Follow-Up.

Not proven: the SSpec-side failure was not re-reproduced (a system-level browser
spec is unaffordable while the priority bootstrap holds the box; 195 concurrent
`simple test` processes were measured during this session).

Status: OPEN (harness gap, P3). Recommend re-tagging out of the
silently-wrong-results class.
