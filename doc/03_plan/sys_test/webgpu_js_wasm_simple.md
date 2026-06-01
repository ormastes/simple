# WebGPU JS/WASM/Simple System Test Plan

## Scope

This plan verifies the current WebGPU browser slice across three consumer paths:

- JavaScript page APIs: `window.isSecureContext`, `navigator.gpu`, `navigator.gpu.requestAdapter`, and canvas `webgpu` context exposure.
- Simple script APIs: direct Simple imports of WebGPU context/resources/commands and canvas wrappers.
- WebAssembly path: Simple-to-WASM backend/glue correctness and a planned browser JS glue bridge that can instantiate a WASM module before using WebGPU-facing page APIs.

Out of scope until implementation exists: real browser GPU driver execution, pixel-stable triangle rendering, full WebGPU CTS, WebGL compatibility, Three.js/Babylon integration, and WASM-originated direct calls into WebGPU host bindings.

## Requirements

| REQ | Requirement | Existing Evidence | Gap |
|-----|-------------|-------------------|-----|
| REQ-WGPU-001 | Secure pages expose `navigator.gpu` and insecure pages hide/block it. | `test/unit/browser/script/navigator_api_spec.spl`, `test/unit/lib/common/web/browser_session_spec.spl` | Add system spec example that asserts both secure and insecure JS page behavior in one flow. |
| REQ-WGPU-002 | Secure canvas `getContext("webgpu")` configures, presents, creates shader modules and render/compute pipelines. | `test/unit/browser/script/canvas_api_spec.spl`, `test/feature/web_platform/webgpu/webgpu_context_spec.spl` | Add system spec example that treats canvas as the browser API boundary. |
| REQ-WGPU-003 | WebGPU resources and command queues validate usage, bounds, invalid ordering, and atomic submit behavior. | `test/feature/web_platform/webgpu/webgpu_resources_spec.spl`, `test/feature/web_platform/webgpu/webgpu_commands_spec.spl` | Add integrated resource + queue example from the Simple script path. |
| REQ-WGPU-004 | Software executor deterministically replays writes, render/compute passes, copies, and rejects invalid sequencing. | `test/feature/web_platform/webgpu/webgpu_software_executor_spec.spl`, `test/unit/browser/script/canvas_api_spec.spl` | Add end-to-end Simple script example that verifies checksums/counters after queue execution. |
| REQ-WGPU-005 | Browser JS session exposes WebGPU globals without regressing regular JS execution. | `test/unit/browser_engine/js_integration_spec.spl`, `test/unit/lib/common/web/browser_session_spec.spl` | Add JS expression examples for `requestAdapter` shape and secure metadata. |
| REQ-WGPU-006 | WASM backend emits browser-compatible WAT/JS glue. | `test/integration/compiler/wasm_e2e_spec.spl`, `test/unit/compiler/wasm_codegen_spec.spl`, `test/feature/usage/wasm_compile_spec.spl` | Direct WASM-originated calls into WebGPU host bindings are not implemented. |
| REQ-WGPU-007 | A browser page can load WASM glue and then use JS WebGPU APIs in the same session. | `webgpu_js_wasm_simple_spec.spl` and `browser_session_fetch_wasm_chain_spec.spl` cover `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` with deterministic module/instance metadata in the same secure BrowserSession. | Remaining bridge work is direct WASM-to-WebGPU host binding calls, not browser-side JS asset loading/instantiation. |

## Execution Order

1. Core WebGPU primitives:
   - `src/compiler_rust/target/debug/simple test test/feature/web_platform/webgpu/webgpu_context_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/feature/web_platform/webgpu/webgpu_resources_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/feature/web_platform/webgpu/webgpu_commands_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/feature/web_platform/webgpu/webgpu_status_errors_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/feature/web_platform/webgpu/webgpu_software_executor_spec.spl --mode=interpreter`
2. Script/browser API:
   - `src/compiler_rust/target/debug/simple test test/unit/browser/script/canvas_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/unit/browser/script/navigator_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/unit/browser/script/worker_api_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/unit/lib/common/web/browser_session_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/unit/browser_engine/js_integration_spec.spl --mode=interpreter`
3. WASM backend:
   - `src/compiler_rust/target/debug/simple test test/integration/compiler/wasm_e2e_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/unit/compiler/wasm_codegen_spec.spl --mode=interpreter`
   - `src/compiler_rust/target/debug/simple test test/feature/usage/wasm_compile_spec.spl --mode=interpreter`
4. New examples:
   - `src/compiler_rust/target/debug/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter`

## Pass/Fail Criteria

PASS for the current slice requires REQ-WGPU-001 through REQ-WGPU-007 to pass with real assertions and no `pass_todo`/placeholder assertions. Direct WASM-to-WebGPU host binding calls remain a documented later bridge layer until an import contract and host binding surface are implemented.

## Traceability

| REQ | Test File | Test Cases | Coverage |
|-----|-----------|------------|----------|
| REQ-WGPU-001 | `navigator_api_spec.spl`, `browser_session_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current metadata API |
| REQ-WGPU-002 | `canvas_api_spec.spl`, `webgpu_context_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current software-backed API |
| REQ-WGPU-003 | `webgpu_resources_spec.spl`, `webgpu_commands_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current validation API |
| REQ-WGPU-004 | `webgpu_software_executor_spec.spl`, `canvas_api_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for deterministic executor |
| REQ-WGPU-005 | `browser_session_spec.spl`, `js_integration_spec.spl`, `webgpu_js_wasm_simple_spec.spl` | 3+ | Full for current JS globals |
| REQ-WGPU-006 | `wasm_e2e_spec.spl`, `wasm_codegen_spec.spl`, `wasm_compile_spec.spl` | 3+ | Full for current backend/glue helper coverage |
| REQ-WGPU-007 | `webgpu_js_wasm_simple_spec.spl`, `browser_session_fetch_wasm_chain_spec.spl` | 2 | Full for JS-mediated BrowserSession WASM asset loading and instantiation |

## Risk Areas

- Interpreter mode may load specs without exercising every `it` body in some runner paths; use native/full execution where available before release.
- BrowserSession now proves JS-mediated WASM fetch, `arrayBuffer`, Promise chaining, and instantiation, but not direct WASM imports that call WebGPU host bindings.
- WASM tests prove backend/glue generation and browser-side instantiation, not a direct WASM-to-WebGPU host binding ABI.
- Current WebGPU executor is deterministic software simulation, not a hardware GPU backend or CTS-compliant renderer.
