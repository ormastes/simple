# Runtime Large ArrayBuffer Probe Resume Plan

Status: DONE (2026-06-18) — focused regression, requirements/NFR traceability,
and guide-applicability evidence recorded for the bounded sparse
ArrayBuffer/Uint8Array runtime slice.

## Context

Fresh session continuation for crashed rollout
`019e829b-fa15-7f70-b873-8ef7c8a7b3aa`; do not resume that rollout.

Lane: BrowserSession/runtime large `ArrayBuffer` and `Uint8Array` probe.

Related existing docs:

- `doc/03_plan/platform/webgpu_js_wasm_simple.md`
- `doc/03_plan/agent_tasks/browser_wasm_webgpu_infra.md`
- `doc/08_tracking/bug/browser_session_uint8array_slice_copy_buffer_2026-06-04.md`
- `doc/08_tracking/bug/browser_webgpu_js_wasm_spec_perf_2026-06-14.md`

## Current Source State

Touched source:

- `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`

Applied bounded fix:

- `ArrayBuffer(length)` no longer eagerly writes one zero property per byte.
- `new Uint8Array(length)` no longer eagerly writes one zero property per byte.
- Existing object-layer lazy indexed reads already return `0` for unset in-range
  `ArrayBuffer` and typed-array bytes, so construction can remain O(1) while
  writes still materialize touched indexes.

Focused check already run:

```bash
SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl
```

Result: PASS.

Focused regression added:

- `test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl`
- `doc/06_spec/test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.md`

The regression proves that a 4096-byte `ArrayBuffer` and its `Uint8Array` view
do not add one object-store property per byte, while unset reads still return
`0` and one view write still normalizes into the backing buffer.

Focused regression check already run:

```bash
SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter
```

Result: PASS, 1 test.

SPipe/doc guards already run:

```bash
bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --output doc/06_spec
sh scripts/setup/install-spipe-dev-command.shs --check
find doc/06_spec -name '*_spec.spl' | wc -l
```

Results: doc generated, `STATUS: PASS spipe-dev-command wiring`, and `0`.

## Next Session Scope

Completion note 2026-06-18:

- Re-ran the focused large-buffer regression:
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter`
- Result: PASS from unchanged-test cache, 1 file passed, 0 failed.
- The implementation and generated manual listed above already existed, and no
  backing-buffer or WASM memory behavior changed in this cleanup lane, so the
  optional WASM host check was not required.
- Final requirements and NFR traceability were added:
  `doc/02_requirements/feature/runtime_large_arraybuffer_probe_resume.md` and
  `doc/02_requirements/nfr/runtime_large_arraybuffer_probe_resume.md`.
- Guide applicability: no `doc/07_guide` update is required for this cleanup
  lane because it changes no public API, command, wrapper, or operator process.
  The canonical reproduction path is the generated SSpec manual:
  `doc/06_spec/test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.md`.
  Broader WebAssembly.Memory/WebGPU guidance remains covered by the separate
  browser/WASM/WebGPU plans and is intentionally not claimed by this row.

This plan is complete for the bounded sparse large-buffer runtime slice. Treat
unrelated dirty files as other-lane work.

Recommended next step:

1. Run the focused large-buffer regression after any follow-up runtime edits.
2. Run the existing WebAssembly.Memory sharing check only if object-layer or
   backing-buffer behavior changes again.
3. If a check fails, make one bounded fix or write one precise repro bug, then
   stop.

Smallest candidate checks:

```bash
SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_large_arraybuffer_spec.spl --mode=interpreter
```

If backing-buffer or WASM memory behavior changes, also use:

```bash
SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_wasm_host_spec.spl --mode=interpreter
```

If the next session needs the end-to-end browser/WASM/WebGPU path:

```bash
SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter
```

Prefer the one-case large-buffer unit spec first because the WebAssembly host
and WebGPU system specs are known slow.

## Historical Stop Conditions

- Do not run repeated green checks.
- Do not run the broad WebGPU system spec more than once.
- Stop after one bounded source fix or one precise repro bug.
- Do not commit or push without explicit user instruction.
