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

## Triage 2026-11-25 (lane p3-bab, worktree wt-p3-bab, release/1.0.0)

Two of the 2026-09-13 triage facts are now outdated on the tracked
`bin/simple.exe` (38,403,072 bytes, `SIMPLE_LIB=src ... --mode=interpreter`):

- The baseline spec no longer fails at import resolution (E1034 is gone):
  `webgpu_js_wasm_simple_spec.spl` loads and executes. It does NOT complete
  on this Windows host, however — `SPEC FILE VERDICT ... executed=1
  passed=0 failed=1 timeout=1 reason=outer-bound-timeout
  budget_ms=930000` (killed at the 930 s outer bound). So the baseline is
  runnable but its green status could not be re-verified here.
- The exact queue-upload evidence this entry asked for now EXISTS as real
  assertions in the broad spec: the example at
  `webgpu_js_wasm_simple_spec.spl:728-731` instantiates a WASM module,
  wraps `i.exports.memory.buffer` in `Uint8Array`, calls
  `device.queue.writeBuffer(target, 4, source, 0, 3)` and asserts
  `"3:1:1:4:3:39:0,0,0,0,12,13,14,0:1:4:3:39"` — offset 4, checksum 39,
  bytes 12,13,14 from WASM memory, plus `adapter.requestDevice()` coverage
  at lines 696-723. (Doc's "byte length 65536" phrasing referred to the
  65536-byte WASM memory the bytes come from; the recorded write length is
  3.)

Left OPEN, narrowed: what remains unproven is (a) a green full-spec run of
the broad spec on a current binary (exceeds the 930 s bound on this host)
and (b) the originally-filed standalone nested-Promise SSpec harness gap
itself, which was not re-exercised here. Not closed on the strength of
source inspection alone.
