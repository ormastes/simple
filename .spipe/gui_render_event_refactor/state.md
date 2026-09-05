# Feature: GUI Render Event Refactor

## Raw Request

$sp_dev  refactor and optimize gui system, do with spawn agent in pherallel,most of all make small change to check gpu event target check. and rendering, event works, draggable windows works.
do architectural refactoring to meet the arch diagram.
prepare logic to migrate to gpu/cpu support logic.
do migrate gpu is to do on later job.
Rename on arch or code to meet
let simple 2d takes draw ir in adv interface and draw ir embedding config(size, location, layer, transparency..). compost draw ir can be a windows even window manager.
need new logic to send event handling event to draw processing components and takes event location and component. and cache event translations but prevent stale translation caching,

## Task Type

code-quality

## Refined Goal

Refactor the Simple UI render/event boundary so Simple 2D has a typed advanced Draw IR contract with embedding metadata, event target translation is cacheable but invalidated by scene changes, and existing rendering/event/draggable-window behavior remains verified without implementing the later GPU backend migration.

## Acceptance Criteria

- AC-1: A typed Draw IR contract exists in the shared UI layer and includes embedding config fields for size, location, layer, transparency, and surface/component identity.
- AC-2: The Simple 2D advanced boundary can accept Draw IR batches through pure Simple code, with a CPU-compatible fallback path and explicit GPU/backend target metadata for later migration.
- AC-3: Event handling can translate an input location into a draw/UI component target, produce an event callback id or target id for dispatch, and map that target into Draw IR draw-processing context.
- AC-4: Event target translation uses a cache key that includes scene or layout revision data so stale translations are rejected after window movement, resize, layer, or composition changes.
- AC-5: Focused tests prove the event target check works for CPU/GPU target metadata, rendering contracts still build, existing event dispatch still works, and draggable window behavior still updates window position.
- AC-6: Architecture documentation names match the new Draw IR and render optimization plugin direction.
- AC-7: The change does not implement real GPU migration; GPU execution remains a later backend job behind the contract.
- AC-8: Draw IR carries source/style provenance for manual, GUI AST, HTML AST/CSS, and WM-generated batches so conversion, cache invalidation, and GPU plugin grouping can be hardened without parsing HTML/CSS in the backend.
- AC-9: Any inefficiency or bug discovered while hardening the GPU/backend path is recorded as a concrete bug report.
- AC-10: Engine2D backend architecture separates drawing backend responsibilities from processing/compute backend responsibilities so future GPU Draw IR migration does not conflate framebuffer ownership with kernel/offload execution.

## Scope Exclusions

- Real OpenCL/CUDA/HIP/Vulkan/Metal/WebGPU execution.
- Replacing the current HTML parser or browser shell.
- Large wrapper rewrites for Electron, Tauri, Chrome, or native host windows.
- Reverting unrelated dirty work in the shared checkout.

## Phase

dev-done

## Log

- dev: Created state file with 7 acceptance criteria (type: code-quality).
- impl: Added pure Simple Draw IR contract, cache-aware window event target
  translation, host WM bridge target metadata, and focused unit/integration
  coverage. GPU execution remains out of scope for a later backend job.
- impl: Added WM scene to Draw IR composition and a standalone Engine2D advanced
  Draw IR executor with CPU fallback metadata and pixel readback evidence.
- impl: Added Draw IR source/style provenance for GUI AST, HTML AST/CSS, manual,
  and WM scene generated batches; updated architecture docs and focused tests.
- bug: Recorded Engine2D Draw IR free-function state visibility risk in
  `doc/08_tracking/bug/engine2d_draw_ir_free_function_state_visibility_2026-06-05.md`.
- impl: Added `DrawIrEventTargetContext` so translated pointer events carry
  component/local coordinate/backend metadata into the Draw IR batch selected
  for draw processing, with stale scene rejection.
- impl: Added `backend_lane.spl` to make drawing vs processing backend
  responsibilities explicit and exported through Engine2D.
