# Browser WebGPU Queue WASM Memory SSpec Promise Harness Gap

Date: 2026-06-14
Status: open (re-triaged 2026-09-13 — see the note at the end of this file)
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

## Triage 2026-09-13 — LEFT OPEN (cannot be exercised on this host)

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the broad spec this entry leans on as its green baseline, `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`, no longer runs here at all — `executed=0`, outcome=ERROR, `cannot resolve import 'plugins.backend_wasm.wasm_codegen_adapter'` (E1034). With the baseline down there is nothing to compare a new SSpec scenario against.
- **inferred**: the gap as filed is an SSpec harness limitation around nested Promise chains, needing a settled-Promise drain helper. That is unchanged work — no fix has landed that would close it, and the runtime support it cites (`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`) still exists.
- Verdict: OPEN — genuinely unresolved, and additionally blocked here by the baseline spec's import failure.
