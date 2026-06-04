# WebGPU JS/WASM/Simple System Test Plan

## Scope

This plan verifies the current WebGPU browser slice across three consumer paths:

- JavaScript page APIs: `window.isSecureContext`, `navigator.gpu`, `navigator.gpu.requestAdapter`, and canvas `webgpu` context exposure.
- Simple script APIs: direct Simple imports of WebGPU context/resources/commands and canvas wrappers.
- WebAssembly path: Simple-to-WASM backend/glue correctness, BrowserSession WASM asset instantiation, JS WebGPU global access in the same session, and a bounded direct WASM import call into a declared WebGPU host binding.

Out of scope until implementation exists: real browser GPU driver execution, pixel-stable triangle rendering, full WebGPU CTS, WebGL compatibility, Three.js/Babylon integration, and a complete WASM-originated WebGPU ABI beyond the declared host-import call contract.

## Requirements

| REQ | Requirement | Existing Evidence | Gap |
|-----|-------------|-------------------|-----|
| REQ-WGPU-001 | Secure pages expose `navigator.gpu` and insecure pages hide/block it. | `test/01_unit/browser/script/navigator_api_spec.spl`, `test/01_unit/lib/common/web/browser_session_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | No current gap for the software-backed metadata API. |
| REQ-WGPU-002 | Secure canvas `getContext("webgpu")` configures, presents, creates shader modules and render/compute pipelines. | `test/01_unit/browser/script/canvas_api_spec.spl`, `test/03_system/feature/web_platform/webgpu/webgpu_context_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | No current gap for the software-backed API. Hardware-backed rendering remains out of scope. |
| REQ-WGPU-003 | WebGPU resources and command queues validate usage, bounds, invalid ordering, and atomic submit behavior. | `test/03_system/feature/web_platform/webgpu/webgpu_resources_spec.spl`, `test/03_system/feature/web_platform/webgpu/webgpu_commands_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | No current gap for the validation API. Full CTS conformance remains out of scope. |
| REQ-WGPU-004 | Software executor deterministically replays writes, render/compute passes, copies, and rejects invalid sequencing. | `test/03_system/feature/web_platform/webgpu/webgpu_software_executor_spec.spl`, `test/01_unit/browser/script/canvas_api_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | No current gap for deterministic software execution. Hardware/driver execution remains out of scope. |
| REQ-WGPU-005 | Browser JS session exposes WebGPU globals without regressing regular JS execution. | `test/01_unit/browser_engine/js_integration_spec.spl`, `test/01_unit/lib/common/web/browser_session_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | No current gap for JS global and adapter metadata coverage. |
| REQ-WGPU-006 | WASM backend emits browser-compatible WAT/JS glue. | `test/02_integration/compiler/wasm_e2e_spec.spl`, `test/01_unit/compiler/wasm_codegen_spec.spl`, `test/03_system/feature/usage/wasm_compile_spec.spl`, and `webgpu_js_wasm_simple_spec.spl` cover bounded exports plus a declared `webgpu.requestAdapter` host import call. | Complete WebGPU host ABI and driver-backed execution are not implemented. |
| REQ-WGPU-007 | A browser page can load WASM glue and then use JS WebGPU APIs in the same session. | `webgpu_js_wasm_simple_spec.spl` and `browser_session_fetch_wasm_chain_spec.spl` cover `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate`, deterministic module/instance metadata, WebGPU global metadata reached from that chain, `requestAdapter()` metadata in the same session, nested returned-Promise assimilation for WebGPU callbacks, fail-closed unsupported imports, and a direct declared WASM-to-JS host import callback. | Remaining bridge work is a full WebGPU binding surface, not browser-side asset loading/instantiation, nested promise assimilation, or minimal host import invocation. |

## Execution Order

1. Core WebGPU primitives:
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/web_platform/webgpu/webgpu_context_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/web_platform/webgpu/webgpu_resources_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/web_platform/webgpu/webgpu_commands_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/web_platform/webgpu/webgpu_status_errors_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/web_platform/webgpu/webgpu_software_executor_spec.spl --mode=interpreter`
2. Script/browser API:
   - `src/compiler_rust/target/debug/simple test test/01_unit/browser/script/canvas_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/01_unit/browser/script/navigator_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/01_unit/browser/script/worker_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/01_unit/browser_engine/js_integration_spec.spl --mode=interpreter`
3. WASM backend:
   - `src/compiler_rust/target/debug/simple test test/02_integration/compiler/wasm_e2e_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/01_unit/compiler/wasm_codegen_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/wasm_compile_spec.spl --mode=interpreter`
4. New examples:
   - `src/compiler_rust/target/debug/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter`

## Pass/Fail Criteria

PASS for the current slice requires REQ-WGPU-001 through REQ-WGPU-007 to pass with real assertions and no `pass_todo`/placeholder assertions. The browser promise chain must reach WASM instantiation metadata and WebGPU global metadata, `requestAdapter()` must resolve deterministic software-adapter metadata in the same session, nested returned-Promise assimilation for WebGPU callbacks must be covered, and the minimal declared WASM-to-WebGPU host import call must be covered. A complete WebGPU host binding surface remains documented later bridge work.

## Traceability

| REQ | Test File | Test Cases | Coverage |
|-----|-----------|------------|----------|
| REQ-WGPU-001 | `navigator_api_spec.spl`, `browser_session_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current metadata API |
| REQ-WGPU-002 | `canvas_api_spec.spl`, `webgpu_context_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current software-backed API |
| REQ-WGPU-003 | `webgpu_resources_spec.spl`, `webgpu_commands_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current validation API |
| REQ-WGPU-004 | `webgpu_software_executor_spec.spl`, `canvas_api_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for deterministic executor |
| REQ-WGPU-005 | `browser_session_spec.spl`, `js_integration_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current JS globals |
| REQ-WGPU-006 | `wasm_e2e_spec.spl`, `wasm_codegen_spec.spl`, `wasm_compile_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 4+ | Full for current backend/glue helper coverage and bounded host import invocation |
| REQ-WGPU-007 | `webgpu_js_wasm_simple_spec.spl`, `browser_session_fetch_wasm_chain_spec.spl` | 5 | Full for JS-mediated BrowserSession WASM asset loading, instantiation, WebGPU global metadata, same-session adapter resolution, nested returned-Promise assimilation, and minimal declared host import callback |

## Risk Areas

- Interpreter mode may load specs without exercising every `it` body in some runner paths; use native/full execution where available before release.
- BrowserSession now proves JS-mediated WASM fetch, `arrayBuffer`, Promise chaining, instantiation, same-session WebGPU global/adapter metadata, nested returned-Promise assimilation for WebGPU callbacks, and a minimal declared `webgpu.requestAdapter` host import callback, but not a complete WebGPU host binding ABI.
- WASM tests prove backend/glue generation, browser-side instantiation, and bounded import invocation, not real hardware WebGPU execution.
- Current WebGPU executor is deterministic software simulation, not a hardware GPU backend or CTS-compliant renderer.
