# Browser WASM WebGPU Infra Completion Audit - 2026-06-14

## Status

STATUS: INCOMPLETE

This audit checks the persistent user objective against current repo evidence.
It does not replace final feature/NFR requirement selection.

## Requirement Evidence

| Objective item | Current evidence | Audit result |
|----------------|------------------|--------------|
| Detailed local/domain research for WebAssembly, WebGPU, Simple browser, and GPU codegen connection points | `doc/01_research/local/browser_wasm_webgpu_infra.md`; `doc/01_research/domain/browser_wasm_webgpu_infra.md` | Proven enough for this lane |
| Small tasks and model assignment, with parallel review | `.spipe/browser-wasm-webgpu-infra/state.md` task/model matrix and review log entries | Proven for planning and repeated review attempts; Opus specifically is not available in this tool environment, so reviews used strongest available `gpt-5.5` |
| Simple browser WASM beside JavaScript | `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl`; `doc/06_spec/01_unit/lib/common/web/browser_session_wasm_script_spec.md` | Proven for inline/external `application/wasm` records and ordered JS continuation |
| Simple browser simple script beside JavaScript | `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl`; `src/lib/gc_async_mut/web/browser_session_loading.spl` | Proven for `type="text/simple"` title/body/Simple2D/Simple3D commands and deterministic warnings |
| Simple 2D interface for Simple script and logic | `src/lib/gc_async_mut/gpu/browser_engine/script/canvas_api.spl`; `webgpu_js_wasm_simple_spec.spl`; `browser_session_simple_script_spec.spl` | Proven for command summaries, Canvas2D JSON, and WebGPU submission records |
| Simple 3D browser facade through WebGPU | `Simple3DContext` in `canvas_api.spl`; `webgpu_js_wasm_simple_spec.spl` | Proven for encoded scene upload bytes/checksum and bounded submit counters; not full semantic 3D rasterization |
| WASM fetch -> instantiate -> same-session WebGPU metadata | `test/01_unit/lib/common/web/browser_session_wasm_fetch_bridge_spec.spl`; broad `browser_session_fetch_wasm_chain_spec.spl`; `webgpu_js_wasm_simple_spec.spl` | Proven for JS-mediated loading, instantiation, metadata, adapter metadata, Promise assimilation, and bounded `webgpu.requestAdapter`/`webgpu.dispatch`/`webgpu.writeBuffer` host-import callbacks with WASM-originated workgroup dimensions, store8/store16/store32 memory payload bytes, Simple2D rectangle payload bytes, and exported `WebAssembly.Memory` buffer reads |
| Browser-shaped WebGPU device queue/compute submit | `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`; `webgpu_js_wasm_simple_spec.spl`; `doc/08_tracking/bug/browser_webgpu_queue_wasm_memory_sspec_promise_2026-06-14.md` | Runtime and SSpec prove bounded software `adapter.requestDevice()`, `device.createBuffer({size, usage})`, `device.queue.writeBuffer(buffer, offset, Uint8Array, sourceOffset, size)` mutating observable buffer bytes/counts/checksums, exported WASM-memory queue upload, compute-shaped WGSL/pipeline/encoder/pass/dispatch/queue-submit counters with multi-pass accumulation and invalid active-pass command-buffer filtering, and WASM-originated dispatch dimensions forwarded into a compute pass |
| Chrome Simple2D/Simple3D WebGPU drawing evidence | `test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl`; `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl` | Host-adaptive proof exists; positive non-fallback hardware pixels depend on local Chrome/WebGPU availability |
| Chrome WebGPU processing/codegen like CUDA with WASM-backed generation | `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl`; `test/01_unit/browser_engine/chrome_webgpu_compute_evidence_spec.spl`; `test/03_system/app/browser/feature/browser_webgpu_chrome_compute_evidence_spec.spl` | Proven for WebGPU/WGSL source-only plan, compiler-emitted WGSL `u32_add` source handoff into the Chrome compute helper, and host-adaptive Chrome compute evidence; not a complete hardware-required CUDA-equivalent runtime |
| GPU process codegen backend order: Vulkan first, then Metal, CUDA/HIP, OpenCL, WebGPU | `src/compiler/70.backend/backend/gpu_portable_compute.spl`; `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl`; `doc/03_plan/platform/webgpu_js_wasm_simple.md` | Proven for dedicated Vulkan boundary and portable Metal -> CUDA -> HIP -> OpenCL -> WebGPU/WGSL source ordering |
| Final SPipe feature and NFR requirements | Option docs exist: `doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md`; `doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md` | Missing: user has not selected final feature/NFR options, so final requirement docs must not be written yet |
| Release-grade verification | `doc/09_report/browser_wasm_webgpu_infra_verification_2026-06-14.md` | WARN: focused gates pass, but final requirements, positive hardware evidence, and unrelated broad `src/lib` check blockers remain open |

## Blocking Selection

The user must choose one feature option and one NFR option before final
requirements can be written:

- Feature: Option A, B, or C from
  `doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md`
- NFR: Option 1, 2, or 3 from
  `doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md`

Recommended default based on current evidence is Feature Option B plus NFR
Option 2. That recommendation is not applied automatically because repo rules
require explicit user selection.

## Open Completion Gaps

- Final `doc/02_requirements/feature/browser_wasm_webgpu_infra.md` and
  `doc/02_requirements/nfr/browser_wasm_webgpu_infra.md` are missing.
- Positive Chrome non-fallback hardware WebGPU draw/compute evidence remains
  host-dependent.
- A complete WASM-originated WebGPU binding ABI remains future work beyond the
  bounded declared adapter/dispatch host-import callbacks with WASM-provided
  workgroup dimensions and buffer payload bytes.
- Broad `bin/simple check src/lib` is blocked by unrelated pre-existing Skia
  export errors, already noted in `.spipe/browser-wasm-webgpu-infra/state.md`.
