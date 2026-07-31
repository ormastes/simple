# Feature: Draw IR Web Renderer Reconciliation

## Raw Request

`$sp_dev remake plan do the all item tasks in pherallel`; sync GitHub and match
the changed Draw IR/Web rendering design to the new plan.

## Task Type

feature

## Refined Goal

Complete reconciliation R1–R9 so production Web, GUI, and WM compositions use
one persistent Engine2D Draw IR executor with canonical text material, complete
typed command handling, honest backend batching/readback, and retained live
evidence.

## Acceptance Criteria

- AC-1: The production browser consumes the supplied `DrawIrComposition`,
  retains one Engine2D owner across two frames, and shuts it down once without
  reparsing HTML or rebuilding a private pixel artifact.
- AC-2: Pointer-down and wheel events traverse the same stable parent ancestry,
  and canonical Web, widget, and WM commands carry nonempty `parent_id` and
  `hit_rect` metadata.
- AC-3: Every remaining iframe pixel render/blit caller migrates to admitted
  composition embedding only after exact CPU-reference parity; script,
  network, and input authority remain fail-closed.
- AC-4: Draw IR TEXT reaches `draw_text`; enabled vector text creates transient
  `FontRenderer`/`FontRenderBatch` material, bitmap-default text creates none,
  and producers cannot call private glyph raster/blit helpers or serialize
  atlas/cache state.
- AC-5: RECT, TEXT, EDGE, PATH, IMAGE, GROUP, and PORT each execute through the
  shared executor or return a typed fail-closed rejection; schema constants
  alone do not count as coverage. Production stays on v2 until a typed v2/v3
  adapter, v3 executor, and exact parity all pass.
- AC-6: Widget and Web producers avoid traversal/concatenation copies using
  existing mutable capacity-aware collections, with retained allocation,
  frame-time, and max-RSS results for 64, 1K, and 10K commands.
- AC-7: Vulkan, CUDA, and Metal perform real compatible batching with retained
  resources and backend-owned receipts; software/CPU-SIMD remain explicitly
  labelled parity oracles rather than GPU proof.
- AC-8: Supported backends expose device-region readback; strict GPU requests
  fail closed without silent CPU fallback, and receipts distinguish
  device-region, full-device, and host-crop paths.
- AC-9: The Linux and macOS matrix retains fresh provenance-bound rows with
  exact device pixels/parity, stable positive device identity where required,
  warm timing, and max RSS; unavailable external-host rows remain active with
  owner, prerequisite, exact resume command, and artifact paths.
- AC-10: Executable SSpecs use the frozen manual steps and helpers below, each
  changed scenario has a mirrored zero-stub operator manual, and no executable
  `.spl` exists under `doc/06_spec`.
- AC-11: Final verification checks rendering source coupling, runtime/env
  boundaries, requirement traceability, current guides/plans/reports/process
  artifacts, and reports PASS only when AC-1–AC-10 have authoritative evidence.
- AC-12: Parallel lanes edit only their assigned owners; the merge owner
  reviews every change, preserves unrelated work, and pushes only verified
  reconciled commits.

## Scope Exclusions

- Engine3D HUD/world as a Web, GUI, WM, or 2D shortcut.
- Draw IR v3 producer cutover before the v2/v3 adapter, executor, and parity
  gate pass.
- New renderer, font cache, event hierarchy, or backend abstraction where the
  existing owners suffice.
- Treating CPU mirrors, screenshots, source contracts, or unavailable hardware
  as native device PASS evidence.

## Cooperative Review

- Lower-model sidecars: R1 lifecycle/cutover; R2 events/metadata; R3 iframe;
  R4 canonical text; R5 executor kinds; R6 allocations; then one disjoint lane
  per R7/R8 backend and one R9 evidence audit lane.
- Merge owner: primary Codex agent in the active reconciliation worktree.
- Final normal/highest-capability reviewer and generated-manual reviewer:
  primary Codex agent after every sidecar handoff.
- Shared interfaces: `DrawIrComposition`,
  `engine2d_draw_ir_adv_composition`, `draw_text`, and
  `RenderBackend.submit_batch`.
- Manual steps: `step("Submit the production Web composition")`,
  `step("Route pointer and wheel through one ancestry")`,
  `step("Embed the iframe composition without a pixel blit")`,
  `step("Render text through canonical Draw IR")`,
  `step("Execute or reject every Draw IR command kind")`,
  `step("Reuse producer storage across frames")`,
  `step("Submit one backend batch and read device pixels")`,
  `step("Read back the requested device region")`, and
  `step("Verify the live rendering matrix")`.
- Setup/checkers: `setup_draw_ir_web_fixture`,
  `expect_composition_submission`, `expect_event_ancestry`,
  `expect_iframe_composition_parity`, `expect_canonical_text_route`,
  `expect_draw_ir_kind_result`, `expect_producer_allocation_budget`,
  `expect_backend_batch_receipt`, `expect_region_readback`, and
  `expect_live_matrix_row`.
- Any unavailable helper must call `assert(false)` or `fail(...)` with the
  missing capability; silent placeholder success is forbidden.

## Runtime Boundary Decision

- runtime_need: no new runtime shortcut is expected.
- facade_checked: existing Draw IR, Engine2D, browser-session, interaction,
  backend submission, and readback owners are mandatory first choices.
- chosen_path: `reuse-facade`.
- rejected_shortcuts: raw app/test `rt_*` calls, fixture-only pixels, direct
  backend proof/status pokes, private browser/widget renderers, synthetic GPU
  handles, and environment-forced success.

## Phase

implementation-partial

## Log

- dev: Refined the authoritative R1–R9 plan into twelve independently testable
  acceptance criteria and froze parallel ownership, interfaces, manual steps,
  helpers, and fail-fast policy.
- implementation: R1, R2, R4, R5, and R8 are source/spec ready but still need
  admitted full-CLI execution. R3 remains RED/pre-migration because its focused
  authenticated parity run crashed with exit 139. R6 retains frame-time and
  max-RSS receipts for 64/1K/10K commands but has no authoritative allocation
  counter. R7 has source batching for CUDA/Metal/Vulkan and a fresh physical
  Vulkan exact-parity unit PASS; broader device/system receipts remain open.
  R9 has a fail-closed aggregate checker, but no fresh complete Linux/macOS
  matrix and physical Metal remains external.
- runtime: Incremental Stage2 compiler admission passed at SHA-256
  `a2c2e3f01c93f571bc3656fde447b18a3bf1293d5f572abd499169eeee5c5f58`.
  Stage3 stopped after one memory-cap failure and one distinct low-memory HIR
  unresolved-symbol failure; no Stage3/full CLI was produced. The deployed
  release CLI also crashed during R3 parity and the final `check src/lib` gate.
- verify: static diff hygiene, frozen vocabulary, `doc/06_spec` layout, and the
  working-tree direct env/runtime guard pass. Overall production readiness is
  still FAIL until the blocked runtime, allocation, backend, and live-matrix
  evidence gates pass.
