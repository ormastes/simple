# Runtime Large ArrayBuffer Probe Resume Requirements

Date: 2026-06-18
Status: selected final requirements for cleanup traceability
Plan: `doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md`

## Scope

This requirement covers the bounded BrowserSession runtime regression where
large JavaScript `ArrayBuffer` and `Uint8Array` construction previously
materialized one object-store property per zero byte. It does not claim full
WebAssembly.Memory, WebGPU, or browser end-to-end parity.

## Requirements

- REQ-RLAB-001: Constructing `ArrayBuffer(length)` for large positive lengths
  must record the byte length and backing-buffer marker without eagerly
  materializing every zero byte as an object-store property.
- REQ-RLAB-002: Constructing `new Uint8Array(buffer)` over an existing
  `ArrayBuffer` must create a view that references the backing buffer without
  copying every zero byte into the view object.
- REQ-RLAB-003: Unset in-range byte reads from the sparse ArrayBuffer and
  Uint8Array view must behave as zero.
- REQ-RLAB-004: Writing one Uint8Array byte must normalize the value to an
  unsigned byte and make the same byte observable through the backing
  ArrayBuffer.

## Evidence

- Implementation: `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`
  and sparse indexed access in
  `src/lib/nogc_sync_mut/js/engine/interpreter_object.spl`.
- Spec: `test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl`.
- Generated manual:
  `doc/06_spec/test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.md`.

