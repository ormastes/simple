<!-- codex-research -->
# Browser WASM WebGPU Infra Local Research

Date: 2026-06-13

## Existing Browser Session Support

- `src/lib/gc_async_mut/web/browser_session.spl` installs browser globals, including secure-context WebGPU metadata and a `WebAssembly` global with validation, compile, instantiate, and streaming entrypoints.
- `src/lib/gc_async_mut/web/browser_session_runtime.spl`, `browser_session_loading.spl`, and `browser_session_modules.spl` own page load, script extraction, script type metadata, external script/module responses, and runtime execution order.
- Existing plan coverage in `doc/03_plan/platform/webgpu_js_wasm_simple.md` already proves the browser-side WASM fetch/arrayBuffer/instantiate chain, WebGPU global metadata, same-session adapter resolution, nested Promise assimilation, and a bounded WASM-to-JS host import callback.

## Existing Browser Engine Script and 2D Support

- `src/lib/gc_async_mut/gpu/browser_engine/browser_script_execute.spl` and `browser_script_render.spl` provide a hardened deterministic script-render path. It handles only narrow inline literal logging and trivial assignments; unsupported script types and external scripts fail closed.
- There is no first-class `type="text/simple"` BrowserSession branch beside JavaScript.
- `src/lib/common/render_scene/scene.spl` defines `RenderScene` and `SceneCommand`; `src/lib/common/render_scene/scene_to_canvas2d_json.spl` serializes that scene model to Canvas2D-style JSON.
- `src/lib/gc_async_mut/gpu/browser_engine/script/canvas_api.spl` currently contains the WebGPU canvas wrapper. A Simple 2D facade can reuse `RenderScene` and Canvas2D JSON as object-state evidence.

## Existing GPU and Codegen Support

- `src/compiler/00.common/gpu_target_metadata.spl` and `src/compiler/35.semantics/gpu_checker.spl` currently recognize `auto`, `cuda`, `hip`, `opencl`, and `vulkan`. They do not expose `metal` or `webgpu` at the compiler front door.
- `src/compiler/70.backend/backend/backend_types.spl` has first-class CUDA, HIP, OpenCL, and Vulkan targets. There is no compiler `Metal` or `WebGPU/WGSL` target yet.
- `src/compiler/70.backend/backend/vulkan_backend.spl` is the strongest non-CUDA compiler seam because it already has a MIR-to-SPIR-V compute path.
- `src/compiler/70.backend/backend/gpu_portable_compute.spl` already models Metal beside CUDA/HIP/OpenCL as a portable source/binary planning target. This is the likely second seam for WebGPU/WGSL emission.
- Runtime/session layers are broader: `src/compiler_rust/gpu/src/device.rs`, `src/lib/gc_async_mut/gpu/engine2d/backend_session.spl`, `backend_probe.spl`, and `sffi_dispatch.spl` name Wgpu/WebGpu, Vulkan, Metal, CUDA, HIP/ROCm, OpenCL, and Software lanes with shader labels such as `wgsl`, `spirv`, `msl`, `ptx`, and `hsaco`.
- Engine3D already treats `webgpu` as a named backend with Chrome-WebGPU-shaped bind groups, textures, and WGSL policy in `src/lib/gc_async_mut/gpu/engine3d/`.

## Recommended Connection Order

1. Vulkan first: it best matches WebGPU storage buffers, workgroups, barriers, bind groups, and compute semantics.
2. Metal second: add WebGPU/WGSL source planning beside portable compute emission where Metal already lives.
3. CUDA/HIP third: consume the shared operation plan after Vulkan/Metal/WebGPU semantics are stable because CUDA/HIP are binary kernel load/dispatch paths.

## Gaps

- No Simple script branch beside JS in `BrowserSession`.
- No Simple 2D browser-script facade beside WebGPU wrappers.
- No compiler-front-door `webgpu` target and no WebGPU processing codegen plan object.
- Existing WebGPU evidence is mostly deterministic browser/session/software metadata rather than hardware execution.

