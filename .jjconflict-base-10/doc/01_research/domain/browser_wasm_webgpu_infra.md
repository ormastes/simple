<!-- codex-research -->
# Browser WASM WebGPU Infra Domain Research

Date: 2026-06-13

## Sources

- W3C WebGPU Candidate Recommendation Draft, 21 May 2026: `https://www.w3.org/TR/webgpu/`
- MDN WebGPU API: `https://developer.mozilla.org/en-US/docs/Web/API/WebGPU_API`
- MDN WebAssembly JavaScript API: `https://developer.mozilla.org/en-US/docs/WebAssembly/Guides/Using_the_JavaScript_API`
- Chrome for Developers WebGPU guide: `https://developer.chrome.com/docs/web-platform/webgpu`

## Findings

WebGPU browser execution is centered on secure-context `navigator.gpu`, adapter/device creation, canvas context configuration, shader modules, pipelines, bind groups, command encoders, and queue submission. Tests must label deterministic software adapters separately from real hardware execution.

WebAssembly browser integration uses JS-owned loading and host imports: fetch bytes, instantiate modules, wire imports, and let JS translate WASM calls into browser APIs such as WebGPU. WASM should not be modeled as directly owning WebGPU objects without an explicit host ABI.

For Simple, the correct bridge is a browser host-ABI plan: Simple-generated WASM exports or host-import calls express draw/compute intent; JS/browser runtime owns WebGPU objects; tests assert command/object evidence rather than screenshots first.

