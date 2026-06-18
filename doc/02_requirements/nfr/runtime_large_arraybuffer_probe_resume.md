# Runtime Large ArrayBuffer Probe Resume NFRs

Date: 2026-06-18
Status: selected final NFRs for cleanup traceability
Plan: `doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md`

## Non-Functional Requirements

- NFR-RLAB-001: Large zero-initialized ArrayBuffer and Uint8Array construction
  must be sparse with respect to the object property store. The focused
  regression gate is a 4096-byte buffer that adds fewer than 8 properties for
  the buffer and fewer than 40 additional properties for the view.
- NFR-RLAB-002: Sparse construction must preserve observable JavaScript byte
  semantics for unset reads and single-byte writes.
- NFR-RLAB-003: The cleanup verification must use the focused unit spec before
  any slower WebGPU or browser end-to-end test, because the affected behavior is
  the object-layer allocation path.

## Evidence

- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter`
- Generated manual:
  `doc/06_spec/test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.md`

