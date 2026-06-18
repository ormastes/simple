# Feature: runtime-large-arraybuffer-probe

## Raw Request

`$sp_dev doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md`

Referenced plan: `doc/03_plan/agent_tasks/runtime_large_arraybuffer_probe_resume.md`

## Task Type

bug

## Refined Goal

Make the BrowserSession JavaScript runtime handle large `ArrayBuffer` and numeric `Uint8Array` construction without eager per-byte zero materialization while preserving existing zero-read and WebAssembly.Memory sharing behavior.

## Acceptance Criteria

- AC-1: `ArrayBuffer(length)` and `new Uint8Array(length)` construction do not eagerly write one zero property per byte in `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`.
- AC-2: In-range reads from unset `ArrayBuffer` and typed-array indexes still return numeric `0`.
- AC-3: Writes through `Uint8Array` views still materialize normalized bytes into their backing `ArrayBuffer`.
- AC-4: Existing WebAssembly.Memory buffer sharing through `Uint8Array` remains covered by a focused executable check.
- AC-5: Resume documentation identifies the current fix, next verification options, and stop conditions for future sessions.
- AC-6: Verification uses one focused runtime check plus required SPipe wiring/layout guards, with no repeated green check loop.

## Scope Exclusions

- Do not resume crashed rollout `019e829b-fa15-7f70-b873-8ef7c8a7b3aa`.
- Do not absorb unrelated dirty files or other active lanes.
- Do not run the broad `webgpu_js_wasm_simple_spec.spl` unless the focused unit check cannot cover the acceptance criteria.
- Do not commit or push without explicit user instruction.

## Phase

dev-done

## Log

- dev: Created state file with 6 acceptance criteria (type: bug).
- spec: Added `test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl`
  to prove large `ArrayBuffer`/`Uint8Array` construction is lazy while unset
  reads and one normalized backing-buffer write still work.
- verify: `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter`
  passed 1/1.
- docgen: Generated `doc/06_spec/test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.md`
  with `bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --output doc/06_spec`.
- guard: `sh scripts/setup/install-spipe-dev-command.shs --check` returned
  `STATUS: PASS spipe-dev-command wiring`.
- guard: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
