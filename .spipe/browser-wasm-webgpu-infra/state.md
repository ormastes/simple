# Feature: browser-wasm-webgpu-infra

## Raw Request
imple web browser infra in webasm, webgpu. $sp_dev make small tasks assign model by difficulty but review by opus. do pherallel agents.  with detail research and webasm, webgpu, and how curren gpu process code gen backend connected to webgpu process.(first consider vulkan, metal, cuda/hip in order)webasm backed code generation.
in chrome, simple 2d/3d(wasm) backed webgpu drawing with webasm
in chrome, webgpu processing backed code generation like cuda backed generation with webasm backed gen.
in simple browser, wasm support beside js.
in simple browser, simple script upport beside js.
in simple browser, simple 2d interface for simple script and logic.
in simple browser,  impl webgpu on simple 2d/3d and gpu process code gen backend

## Task Type
feature

## Refined Goal
Implement browser infrastructure that lets Chrome and the Simple browser run Simple-generated WebAssembly beside JavaScript, expose Simple script beside JavaScript, draw Simple 2D/3D through WebGPU, and route WebGPU processing code generation through the existing GPU backend model with Vulkan, Metal, CUDA/HIP, and WebAssembly/WebGPU ordered as explicit backend lanes.

## Acceptance Criteria
- AC-1: Detailed local and domain research exists for WebAssembly, WebGPU, Simple browser script/WASM support, and current GPU codegen/backend connection points.
- AC-2: The implementation plan is split into small tasks with difficulty, model assignment, owner scope, review scope, and independent verification commands.
- AC-3: Chrome can load Simple-generated WASM and exercise a Simple 2D/3D WebGPU drawing path with non-placeholder DOM/canvas/WebGPU evidence.
- AC-4: Chrome can exercise a WebAssembly-backed WebGPU processing/codegen path analogous to the existing CUDA codegen flow, with explicit unsupported-state diagnostics instead of placeholder generated source.
- AC-5: The Simple browser supports WASM modules beside JavaScript in the same browser session without regressing existing JS execution.
- AC-6: The Simple browser supports Simple script beside JavaScript with a minimal script execution surface and deterministic failure reporting.
- AC-7: The Simple browser exposes Simple 2D and Simple 3D interfaces for Simple script logic and records Draw IR or equivalent object-state evidence for rendered output.
- AC-8: Simple 2D/3D and GPU process codegen backends expose a WebGPU lane while preserving the existing Vulkan, Metal, CUDA/HIP ordering and fallback contracts.
- AC-9: Executable SSpec coverage and generated `doc/06_spec` manuals prove the critical browser/WASM/WebGPU flows with real assertions and no placeholder passes.
- AC-10: Verification includes the generated-spec layout guard, relevant browser/WebGPU/WASM specs, and any compiler/lib/MCP smoke gates triggered by touched files.

## Scope Exclusions
- Full WebGPU CTS conformance is not required for the first complete slice.
- Native hardware WebGPU execution is not required where the host/browser cannot expose it; deterministic software or structured browser evidence is acceptable if labeled and fail-closed.
- “Review by Opus” is mapped to strongest available review model in this environment because Opus is not an available sub-agent model.

## Model Assignment
- Hard architecture/review: `gpt-5.5`, high reasoning, review-only.
- Medium GPU codegen/backend research and implementation slices: `gpt-5.4`, high reasoning.
- Bounded browser/WASM/script inventory and small test/docs tasks: `gpt-5.4-mini`, medium reasoning.

## Small Task Breakdown
- T1 research-browser-wasm-script: inventory BrowserSession, JS, WASM, Simple script, and Simple 2D hooks.
- T2 research-gpu-codegen-webgpu: inventory GPU process/codegen backend connection points and Vulkan/Metal/CUDA/HIP/WebGPU ordering.
- T3 spec-browser-wasm-script: add SSpec scenarios for WASM beside JS and Simple script beside JS.
- T4 spec-webgpu-draw-process: add SSpec scenarios for Chrome/WebGPU drawing and WebGPU processing codegen.
- T5 impl-browser-wasm: wire BrowserSession WASM module execution beside JS.
- T6 impl-simple-script: wire Simple script execution beside JS with deterministic diagnostics.
- T7 impl-simple-2d-3d-script: expose Simple 2D/3D commands to Simple script and capture Draw IR/object evidence.
- T8 impl-webgpu-codegen: add WebGPU processing codegen lane that maps through existing GPU backend contracts and fails closed when unsupported.
- T9 docs-guides-manuals: refresh architecture, design, guides, generated specs, and feature tracking.
- T10 verify-review: strongest-model review, no-placeholder scan, generated-spec layout guard, and targeted test suite.

## Phase
design-implementation-in-progress

## Log
- dev: Created state file with 10 acceptance criteria and 10 small tasks (type: feature).
- impl: Added first Simple 2D browser facade and SSpec evidence in `canvas_api.spl` and `webgpu_js_wasm_simple_spec.spl`.
- impl: Added BrowserSession `type="text/simple"` command execution for title/body/Simple2D evidence with deterministic unsupported-command warnings.
- spec: Added `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl` and generated `doc/06_spec/test/01_unit/lib/common/web/browser_session_simple_script_spec.md`.
- impl: Added compiler GPU target metadata for `metal` and `webgpu` aliases, with `auto` ordering Vulkan -> Metal -> CUDA/HIP -> OpenCL and explicit WebGPU browser/WASM bridge reasoning.
- spec: Updated `test/01_unit/compiler/semantics/gpu_target_contract_spec.spl` and regenerated `doc/06_spec/test/01_unit/compiler/semantics/gpu_target_contract_spec.md`.
- impl: Added explicit opt-in WebGPU/WGSL portable compute target with source-only compile plans, browser host-import diagnostics, dedicated WGSL fill/add and Simple 2D generated-kernel emitters, and backend init exports.
- spec: Updated `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl` for WebGPU source-only evidence and regenerated `doc/06_spec/test/01_unit/compiler/codegen/gpu_portable_compute_spec.md`.
- review: Strongest available review lane confirmed WebGPU should remain metadata/source-plan only and must not be promoted into `BackendKind` or `vulkan_backend.spl` in this slice.
- impl: Added BrowserSession `application/wasm` script resource handling with inline/external WASM module records, validation status, separate `wasm` pending request kind, and ordered resume of later JavaScript.
- spec: Added `test/01_unit/lib/common/web/browser_session_wasm_script_spec.spl` and generated `doc/06_spec/test/01_unit/lib/common/web/browser_session_wasm_script_spec.md`.
- impl: Added Simple2D-to-WebGPU render submission evidence with render-pass/draw-call counters in the browser WebGPU command model and software replay result.
- spec: Updated `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` for Simple2D WebGPU render submission and a guard that `BrowserRenderer.create_with_backend("webgpu")` still reports software fallback instead of overclaiming.
- review: Strongest available review lane confirmed this proves deterministic in-process WebGPU command replay only; true Chrome/Electron pixel-backed WebGPU evidence remains a separate required slice.
- impl: Added separate Chrome/Electron WebGPU draw evidence wrapper in `src/lib/gc_async_mut/gpu/browser_engine/chrome_webgpu_draw_evidence.spl` plus Electron app helper `tools/web-render-backend/chromium-webgpu-draw/`.
- spec: Added parser coverage in `test/01_unit/browser_engine/chrome_webgpu_draw_evidence_spec.spl` and host-adaptive Chrome evidence coverage in `test/03_system/app/browser/feature/browser_webgpu_chrome_draw_evidence_spec.spl`; this host returned explicit unavailable status because no helper JSON was produced. Review found and the slice fixed empty-capture and fallback-adapter overclaim risks.
- docs: Updated `doc/03_plan/platform/webgpu_js_wasm_simple.md`, `doc/07_guide/lib/gpu_3d/webgpu_guide.md`, and `doc/07_guide/ui/web_render_backend.md` to make `chrome_webgpu_draw_evidence` the canonical Chrome WebGPU draw probe and keep `WebRenderBackend("chromium")` scoped to HTML pixel parity.
- impl: Added `canvas_get_context_simple3d`, `Simple3DContext`, command summaries, scene payload bytes/checksum, and WebGPU scene-upload submission evidence beside the existing Simple2D browser facade.
- impl: Extended BrowserSession `text/simple` execution with `simple3d.clear_color`, `simple3d.camera_perspective`, `simple3d.triangle`, and `simple3d.submit_webgpu` commands.
- spec: Updated `test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl` and regenerated `doc/06_spec/test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.md`; the evidence intentionally proves encoded scene upload and submission counters, not full semantic 3D rasterization.
- docs: Updated `doc/03_plan/platform/webgpu_js_wasm_simple.md`, `doc/07_guide/lib/gpu_3d/webgpu_guide.md`, and `doc/07_guide/ui/web_render_backend.md` for the Simple3D facade and its evidence boundary.
- review: Strongest available review found and the slice fixed the earlier Simple3D overclaim by replacing `submitted-webgpu-3d-render` with explicit scene-upload bytes/checksum evidence.
- impl: Replaced unchecked `text/simple` numeric conversion for Simple2D/Simple3D drawing commands with validated decimal parsing and deterministic warning messages.
- spec: Extended `test/01_unit/lib/common/web/browser_session_simple_script_spec.spl` and regenerated its manual so malformed drawing numbers report warnings instead of silently producing partial evidence.
- design: Added missing SPipe design artifacts: `doc/04_architecture/browser_wasm_webgpu_infra.md`, `doc/05_design/browser_wasm_webgpu_infra.md`, `doc/05_design/browser_wasm_webgpu_infra_tui.md`, `doc/05_design/browser_wasm_webgpu_infra_gui.md`, and `doc/03_plan/sys_test/browser_wasm_webgpu_infra.md`.
- gate: Final requirement/NFR docs remain pending user selection from `doc/02_requirements/feature/browser_wasm_webgpu_infra_options.md` and `doc/02_requirements/nfr/browser_wasm_webgpu_infra_options.md`; design currently traces to this state file and the `REQ-WGPU-*` test plan.
- tracking: Added `BROWSER_WASM_WEBGPU_INFRA_2026_06_13` to `doc/08_tracking/feature/feature_db.sdn` with status `current`, option-doc requirement links, research/plan/architecture/design/spec/source/test/guide coverage, and clean `bin/simple lint doc/08_tracking/feature/feature_db.sdn` evidence.
- docs: Updated the three browser WebGPU system spec manuals to point at the new architecture and design artifacts instead of `Design: N/A`; regenerated their `doc/06_spec` mirrors.
- verify: `sh scripts/setup/install-spipe-dev-command.shs --check` passed, `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`, and the touched system specs passed: `webgpu_js_wasm_simple_spec.spl` 114/114, `browser_webgpu_chrome_draw_evidence_spec.spl` 1/1, `browser_webgpu_chrome_compute_evidence_spec.spl` 1/1.
- tracking: Repaired the feature DB row to avoid comma-splitting drift, added readable tracking entries in `doc/08_tracking/feature/feature.md`, `doc/08_tracking/feature/current_feature.md`, and `doc/08_tracking/feature/group/browser_webgpu.md`, and verified `bin/simple lint doc/08_tracking/feature/feature_db.sdn`, direct row visibility in the DB/current/group files, and group-summary visibility in `feature.md`.
- verify: Ran the remaining focused specs from `doc/03_plan/sys_test/browser_wasm_webgpu_infra.md`: `browser_session_wasm_script_spec.spl` 3/3 cached-pass, `browser_session_simple_script_spec.spl` 4/4, `gpu_target_contract_spec.spl` 5/5 cached-pass, `gpu_portable_compute_spec.spl` 24/24, `chrome_webgpu_draw_evidence_spec.spl` 5/5, and `chrome_webgpu_compute_evidence_spec.spl` 6/6 cached-pass.
- review: Parallel strongest-model review found no placeholder assertions and confirmed BrowserSession WASM/Simple-script coverage, but flagged portable compute auto-order evidence and stale duplicate/generated manuals.
- impl: Updated `gpu_portable_compute.spl` so auto portable expansion follows the Vulkan dedicated-backend boundary with Metal -> CUDA -> HIP -> OpenCL -> WebGPU/WGSL source, and extended `gpu_portable_compute_spec.spl` to assert that ordering plus the Vulkan-first diagnostic.
- docs: Regenerated the full lane `doc/06_spec` manual set in one docgen pass, removed stale duplicate manuals under old `doc/06_spec/system/...` and `doc/06_spec/unit/...` paths, expanded the system test plan docgen commands to include all tracked unit specs, and refreshed the spec index date.
- verify: Broader compiler-change gates: `bin/simple check src/compiler` passed all checked files with existing unresolved-export warnings; `bin/simple check src/app/mcp` passed 30 files; `bin/simple check src/app/simple_lsp_mcp` passed 4 files; `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter` passed 1/1 from cache.
- verify-gap: `bin/simple check src/lib` was attempted and failed on unrelated pre-existing broad-tree Skia/export errors, including `src/lib/skia/feature/color_management/icc_writer.spl` missing exported `ICC_MAGIC` and `src/lib/skia/feature/glyph/colrv1_compositor.spl` missing exported `SkColor`; no BrowserSession/WebGPU touched files were reported in the displayed failing tail.
