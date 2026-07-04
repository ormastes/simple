<!-- codex-design -->

# Browser WASM WebGPU Infra Architecture

## Status

Design for the SPipe lane in `.spipe/browser-wasm-webgpu-infra/state.md`.
Final requirement files are still pending user selection from
`doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md` and
`doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md`; this document
therefore traces to the accepted lane ACs and the existing
`doc/03_plan/platform/webgpu_js_wasm_simple.md` `REQ-WGPU-*` test plan.

## Architecture Decision

Use a browser host-ABI bridge instead of making Simple-generated WASM own
browser GPU objects directly.

Simple, Simple script, and Simple-generated WASM produce bounded draw or compute
intent. BrowserSession and the Chrome/Electron helper own browser objects:
`WebAssembly`, `navigator.gpu`, adapters, devices, shader modules, pipelines,
command encoders, queues, and readback buffers. Compiler GPU codegen exposes a
source-plan WebGPU/WGSL lane beside Vulkan, Metal, CUDA/HIP, and OpenCL rather
than promoting WebGPU into the native backend ABI.

## Layering

| Layer | Owner | Contract |
|-------|-------|----------|
| Browser session | `src/lib/gc_async_mut/web/browser_session*.spl` | Load JS, `application/wasm`, and `text/simple` scripts in one ordered page session. Record deterministic WASM and Simple script evidence. |
| Browser script canvas facade | `src/lib/gc_async_mut/gpu/browser_engine/script/canvas_api.spl` | Convert Simple2D and Simple3D commands into bounded object-state and WebGPU submission evidence. |
| WebGPU browser model | `src/lib/gc_async_mut/gpu/browser_engine/script/*webgpu*` | Model secure-context GPU access, context configuration, resources, command validation, software replay, and queue submission. |
| Chrome evidence wrappers | `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_*_evidence.spl` | Execute host-adaptive Chrome/Electron draw and compute probes; return explicit `host-unavailable:*` status when hardware/browser support is absent. |
| Compiler GPU target metadata | `src/compiler/00.common/gpu_target_metadata.spl`, `src/compiler/35.semantics/gpu_checker.spl` | Preserve automatic preference order Vulkan -> Metal -> CUDA/HIP -> OpenCL; require explicit WebGPU opt-in for browser/WASM host import plans. |
| Portable compute planning | `src/compiler/70.backend/backend/gpu_portable_compute.spl` | Emit WebGPU/WGSL source-only compile plans and diagnostics, not native binaries. The browser/WASM bridge plan records the `vulkan(dedicated),metal,cuda,hip,opencl,webgpu` priority boundary and the WebGPU host-import/payload contract. |

## Backend Ordering

Native or driver-backed GPU selection keeps the existing low-level preference:
Vulkan first, then Metal, then CUDA/HIP, then OpenCL/software fallback. The
portable compute planner records Vulkan as a dedicated SPIR-V backend boundary,
then expands portable generated kernels as Metal, CUDA, HIP, OpenCL, and finally
WebGPU/WGSL source. WebGPU is never promoted ahead of native lanes; it remains a
browser target for WASM/JS-hosted WGSL source plans because browser WebGPU
compilation and queue execution happen through `navigator.gpu`, not through the
native backend factory.

This ordering is specific to compiler/browser-hosted portable compute. The
default Pure Simple GUI and Simple2D render path uses the Engine2D backend lane
planner documented in `doc/04_architecture/ui/simple_gui_stack_tldr.md` and
`doc/07_guide/app/ui/engine2d_backend_order.md`: explicit native surfaces stay
caller-owned, while automatic GUI drawing starts at platform-native Metal, then
CUDA/HIP, Qualcomm, Vulkan, DirectX, OpenCL, and CPU fallbacks.

## MDSOC Fit

This lane is a virtual capsule crossing compiler, browser session, browser
engine, and evidence tooling. The capsule boundary is the host-ABI record:
source modules and scripts produce serializable intent; browser/runtime layers
materialize GPU objects and evidence. That avoids sibling-private coupling
between compiler backends and browser renderer internals.

Feature transforms are appropriate for:

- Adding `text/simple` handling beside existing JS script extraction.
- Adding `application/wasm` module records beside existing JS execution order.
- Adding WebGPU target metadata beside existing GPU checker target handling.
- Adding Chrome evidence wrappers beside deterministic in-process WebGPU tests.

## Hot-Path Constraints

Browser request handlers must not perform repeated full-tree scans, shell out to
Chrome, or sleep/retry on ordinary page loads. Chrome/Electron probes stay in
explicit evidence wrappers and system specs. BrowserSession page load remains
in-memory parsing plus declared fetch/module callbacks.

Compiler hot paths must keep WebGPU as a source-plan target. Native backend
selection should not invoke browser tooling or probe `navigator.gpu`.

## Failure Policy

Unsupported states are evidence, not silent fallback:

- Insecure pages hide/block WebGPU metadata.
- Invalid or unsupported WASM records are recorded with validation status.
- Unsupported Simple script commands emit deterministic warnings.
- Host-unavailable Chrome/WebGPU probes return explicit status strings with zero
readback bytes and no software-executor substitution.
- WebGPU codegen plans identify WGSL/source-only output and browser host-import
requirements.
