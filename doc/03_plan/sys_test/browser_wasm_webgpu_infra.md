<!-- codex-design -->

# Browser WASM WebGPU Infra System Test Plan

## Scope

This plan covers the browser/WASM/WebGPU lane described by
`.spipe/browser-wasm-webgpu-infra/state.md`. It extends the focused platform
plan in `doc/03_plan/platform/webgpu_js_wasm_simple.md`.

## Test Matrix

| Requirement Source | Spec | Purpose |
|--------------------|------|---------|
| AC-3, AC-7, REQ-WGPU-002 | `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` | Prove Simple2D and Simple3D browser facade evidence can submit bounded WebGPU render/scene records. |
| AC-4 | `test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl` | Prove Chrome WebGPU compute runs WGSL/readback when available or reports explicit host-unavailable status. |
| AC-3 | `test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl` | Prove Chrome WebGPU draw evidence is separated from deterministic software fallback. |
| AC-5 | `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl` | Prove `application/wasm` scripts load beside JavaScript in one session. |
| AC-5, REQ-WGPU-007 | `test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl` | Prove fetched WASM bytes instantiate and retain same-session WebGPU metadata through the fast BrowserSession bridge gate. |
| REQ-WGPU-007 | `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` | Extended BrowserSession WASM fetch-chain conformance evidence beyond the fast bridge gate. |
| AC-6, AC-7 | `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl` | Prove `text/simple` commands run beside JavaScript and fail deterministically. |
| AC-8 | `test/01_unit/compiler/semantics/gpu_target_contract_spec.spl` | Prove GPU target ordering and explicit WebGPU metadata. |
| AC-4, AC-8 | `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl` | Prove WebGPU/WGSL portable compute source plans and host-import diagnostics. |

## Required Commands

Run focused specs after changes:

```sh
bin/simple test test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl --mode=interpreter
bin/simple test test/01_unit/lib/common/web/browser_session_simple_script_spec.spl --mode=interpreter
bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/semantics/gpu_target_contract_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl --mode=interpreter
bin/simple test test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl --mode=interpreter
bin/simple test test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl --mode=interpreter
bin/simple test test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl --mode=interpreter
bin/simple test test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl --mode=interpreter
```

Run extended broad regression evidence when touching BrowserSession WASM
fetch/compile/instantiate internals:

```sh
bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --timeout-ms=180000
```

Run generated manual and layout guards:

```sh
bin/simple spipe-docgen test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/lib/common/web/browser_session_simple_script_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/compiler/semantics/gpu_target_contract_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl --output doc/06_spec
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Pass Criteria

- All focused specs pass or return documented host-unavailable evidence for
  Chrome/WebGPU probes.
- Generated manuals mirror changed specs and remain readable as operator docs.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
- No placeholder assertions such as `expect(true).to_equal(true)` or
  `pass_todo` appear in touched specs.
