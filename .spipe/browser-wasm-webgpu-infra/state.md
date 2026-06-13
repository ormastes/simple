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
- AC-7: The Simple browser exposes a Simple 2D interface for Simple script logic and records Draw IR or equivalent object-state evidence for rendered output.
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
- T7 impl-simple-2d-script: expose Simple 2D commands to Simple script and capture Draw IR/object evidence.
- T8 impl-webgpu-codegen: add WebGPU processing codegen lane that maps through existing GPU backend contracts and fails closed when unsupported.
- T9 docs-guides-manuals: refresh architecture, design, guides, generated specs, and feature tracking.
- T10 verify-review: strongest-model review, no-placeholder scan, generated-spec layout guard, and targeted test suite.

## Phase
dev-done

## Log
- dev: Created state file with 10 acceptance criteria and 10 small tasks (type: feature).
