# Proposed Plan — Unified Surface Draw IR and HTML/CSS Conformance

Date: 2026-07-29
Status: Vulkan-first UiIr direction selected; NFR option pending

This plan extends rather than replaces:

- `doc/03_plan/ui/webir_drawir_optimization.md`
- `doc/03_plan/ui/rendering/draw_ir_multibackend_plan.md`
- `doc/03_plan/ui/web_browser/pure_simple_web_renderer_chromium_quality_plan.md`

Detailed parallel ownership, tasks, estimates, merge gates, and shared
interfaces are frozen in:

- `doc/03_plan/agent_tasks/unified_surface_draw_ir_and_html_css_conformance.md`

## Selected shared boundary

Option A is refined to use the existing `DrawIrComposition` as the stable
semantic display list and a new compact `UiIr` as the backend execution form:

```
Web/GUI/2D/WM/graphical TUI/CLI
    -> DrawIrComposition
    -> draw_ir_to_ui_ir
    -> UiIr
    -> Vulkan first
    -> CUDA/HIP, Metal, DirectX, and CPU parity
```

Logical producer names do not imply new public display-list structs.

| Surface | Producer-owned state | Graphical lowering |
|---|---|---|
| Simple 2D | primitive/scene state | `simple_2d_to_draw_ir` |
| GUI/UI | retained widget/UI state | `widget_tree_to_draw_ir` (existing) |
| Web | private HTML/CSS semantic/layout state | `simple_web_layout_render_html_draw_ir` (existing) |
| WM | `SharedWmScene` | `shared_wm_scene_draw_ir_composition` (existing) |
| TUI | cell/grid, grapheme, ANSI, cursor state | `tui_grid_to_draw_ir` only for graphical hosting |
| CLI | text/events/exit/stream state | `cli_surface_to_draw_ir` only for graphical hosting |

Do not add new names where an existing function already satisfies the boundary.
New TUI/CLI names are provisional until source design confirms no existing
adapter.

## UiIr data contract

`UiIr` is optimized for Vulkan upload and dispatch while remaining free of
Vulkan objects. The first design uses fixed-width, 16-byte-aligned records and
indexed side tables:

- `UiIr`: schema, revision, viewport, passes, primitives, clips, transforms,
  resources, payload bytes, dirty regions, and evidence regions.
- `UiIrPass`: target/resource indices, primitive range, dirty range, load/store
  policy, and deterministic barrier boundary.
- `UiIrPrimitive`: a 64-byte record containing four 32-bit header/index fields,
  integer bounds, four 32-bit paint/order/payload fields, and four stable
  source/reserved fields.
- `UiIrClip`: flattened integer clip bounds plus parent index.
- `UiIrTransform`: packed 2D transform values; identity is index zero.
- `UiIrResource`: stable resource id, generation, kind, dimensions, format,
  and payload range. Native Vulkan handles remain in the Vulkan session table.

Hot primitive records contain no `text`, nested arrays, optional values, or
backend handles. Text, glyph runs, paths, and images use bounded side-table
ranges. Lowering sorts only inside explicit pass boundaries and preserves
Draw IR order, stable identity, clips, hit/layout ownership, and fallback
policy.

The exact array-of-struct versus structure-of-arrays upload layout is selected
from measured Vulkan evidence before schema freeze. The semantic fields and
validation rules above remain stable.

## GPU execution model

UiIr feeds the existing Engine2D drawing/processing lane contract. It never
assumes that every GPU API presents pixels the same way:

| Backend | UiIr execution | Presentation/readback |
|---|---|---|
| Vulkan | graphics/compute pipelines, first schema/perf target | swapchain or offscreen image plus device readback |
| CUDA | coarse compute batches into a device framebuffer | platform interop or explicit copy/presenter |
| HIP/ROCm | CUDA-equivalent coarse compute batches | platform interop or explicit copy/presenter |
| Metal | render/compute command encoders | drawable or offscreen texture plus device readback |
| DirectX | D3D render/compute command lists | swapchain or staging texture readback |
| CPU/SIMD | reference executor | host framebuffer |

Each executor declares supported UiIr command families. Unsupported work uses
the shared declared fallback and makes the frame mixed; it cannot claim full
GPU execution. CUDA and HIP are one semantic lane with distinct compiled
artifacts and device identities, not duplicated render algorithms.

Backend-private preparation may build descriptor sets, argument buffers,
pipeline state, command buffers, or launch parameters from UiIr. Those prepared
objects are transient caches keyed by UiIr revision plus device capability and
never become another serialized IR.

## Phase 0 — Inventory and freeze

- Build a machine-readable producer-to-command matrix for every Draw IR command,
  style property, image/text path, event target, clip, and embedding mode.
- Record legacy call sites and current semantic/pixel/performance baselines.
- Freeze source-kind values, stable IDs, scene keys, and compatibility outputs.
- Baseline Vulkan upload bytes, dispatches, p50/p95 frame time, max RSS, and
  readback checksum for representative 2D, GUI, and Web scenes.
- Exit: no unknown production rendering path and no unowned legacy fallback.

## Phase 1 — Draw IR to UiIr contract

- Add `src/lib/common/ui/ui_ir.spl` only after the field/layout design passes
  source review.
- Add one `draw_ir_to_ui_ir(composition, limits) -> Result<UiIr, text>`
  lowering owner.
- Validate dimensions, counts, arithmetic, side-table ranges, resource
  generations, clip parents, pass ranges, and deterministic order before any
  device allocation.
- Keep Draw IR serialization/diff/inspection unchanged; UiIr is regenerated or
  cached by Draw IR scene/revision/backend-capability keys.
- Add an independent CPU reference executor for UiIr only if the existing
  Engine2D CPU lane cannot consume it without duplication.
- Exit: GUI, Web, and Simple 2D fixtures produce deterministic UiIr with
  identical semantic bounds/order and exact CPU reference pixels.

## Phase 2 — Vulkan-first execution

- Pack validated UiIr into bounded staging/storage buffers.
- Group primitives by compatible Vulkan pipeline within explicit pass/order
  boundaries.
- Keep descriptors, pipelines, device addresses, fences, swapchains, and
  resource handles inside the existing Vulkan backend/session.
- Implement rectangle/image/text/path command families incrementally; an
  unsupported family fails explicitly or uses the declared CPU fallback.
- Prove device-owned execution with positive backend identity, dispatch counts,
  readback checksum, and no CPU-mirror substitution.
- Exit: the same UiIr fixture matches the CPU reference and improves measured
  Vulkan frame/upload cost without changing Draw IR semantics.

## Phase 3 — GPU executor parity

Order: CUDA, HIP/ROCm, Metal, DirectX. Order may change only when required host
hardware is unavailable; skipped hardware is recorded, never treated as pass.

For each backend:

1. Reuse the UiIr validation, pass ranges, resource generations, clip indices,
   ordering, and fallback schema.
2. Map coarse passes to the backend's existing drawing/processing primitives;
   do not dispatch once per widget or DOM node.
3. Prove the native kernel/pipeline executed, not only that a counter changed.
4. Compare exact deterministic pixels against the CPU UiIr executor.
5. Record upload bytes, dispatch/draw count, accelerated/fallback commands,
   device identity, p50/p95, max RSS, presentation, and readback source.
6. Mark a frame fully GPU-rendered only when all required commands and final
   pixels are device-owned.

Exit: one 2D, GUI, Web, animation, text, image, clip, and mixed-fallback fixture
has honest evidence on every available backend.

## Phase 4 — Producer refactor

- Centralize strict Draw IR validation at the existing shared boundary.
- Require producer-resolved layout/style; executors never parse HTML/CSS or
  widget/TUI/CLI semantics.
- Add missing producer provenance rather than new command trees.
- Exit: all producers either emit valid `DrawIrComposition` or report a precise
  unsupported reason.

Order: Simple 2D, GUI/UI, WM, Web, graphical TUI, graphical CLI.

For each producer:

1. Characterize legacy semantic output and pixels.
2. Route through its existing or minimal `*_to_draw_ir` adapter and the single
   `draw_ir_to_ui_ir` lowering.
3. Dual-run legacy and Draw IR/UiIr in tests.
4. Fix the shared owner when multiple producers expose the same defect.
5. Delete a legacy branch only after semantic, pixel, input, and performance
   parity passes.

No full bootstrap is required. Use the smallest pure-Simple phase capable of
running the affected focused specs.

## Phase 5 — Structure and performance

- Keep web cascade/layout records compact and producer-private.
- Keep GUI retained identity/event state producer-private.
- Keep TUI cells and CLI streams producer-private.
- Use Draw IR diff/patch for graphical incremental updates.
- Lower only changed Draw IR batches/resources into UiIr deltas.
- Cache by scene/style/content/backend/DPI revisions with explicit invalidation.
- Reuse Engine2D transient font, image, clip, and backend material.
- Measure warm frame latency, changed-command count, allocations, retained
  bytes, and max RSS before changing defaults.
- Reject optimizations that create a second renderer or alter unsupported
  semantics.

## Phase 6 — HTML parser and CSS conformance manifests

- Pin WHATWG HTML, CSS Snapshot/module, and WPT revisions.
- Track behaviors, not tag/property names:
  parser/tree recovery, default semantics, cascade, computed/used values,
  layout, paint, interaction, animation, and accessibility.
- Associate every supported feature with specification sections, WPT paths,
  Simple requirements, implementation owner, and executable evidence.
- Keep partial multi-value declarations fail-closed as CSS requires.

## Phase 7 — Modern SSpec system-test migration

Existing `std.spec` scenarios remain; do not rewrite them merely for style.
Modernize evidence in this order:

1. Parser/DOM tree assertions.
2. Cascade/computed/used style assertions.
3. Layout boxes, text fragments, stacking, clipping, and hit targets.
4. `expect_draw`-style Draw IR commands/provenance.
5. Deterministic UiIr pass/primitive/resource records.
6. Exact Engine2D/Vulkan readback pixels for deterministic Simple fixtures.
7. WPT reftest or pinned Chromium comparison with explicit tolerance.
8. Post-load mutation/animation frame evidence after the intended frame.

Every scenario uses canonical matchers, `step("...")`, REQ traceability, and
typed `@capture(html)` where applicable. No status-only, source-only,
placeholder, or inventory-only test may claim rendering conformance.

Frozen manual steps:

- `Parse the standards fixture into the expected document tree`
- `Resolve the expected cascade and used layout values`
- `Lower the surface through the canonical Draw IR boundary`
- `Lower Draw IR into bounded UiIr execution records`
- `Render UiIr through the Vulkan executor`
- `Replay the same UiIr through each available GPU executor`
- `Distinguish full GPU execution from mixed fallback`
- `Compare semantic layout and visible pixels with the reference`
- `Advance the animation to the specified frame`
- `Reject unsupported syntax without partial rendering`

Provisional checker names:

- `expect_document_tree`
- `expect_computed_style`
- `expect_layout_box`
- `expect_draw`
- `expect_ui_ir`
- `expect_rendered_pixels`
- `expect_reference_match`

Unimplemented helpers must call `fail(...)`; they may not return success.

## Phase 8 — Full HTML/CSS implementation order

1. HTML tokenizer/tree construction and error recovery.
2. DOM semantics and UA default styles.
3. CSS syntax, cascade, inheritance, selectors, variables, and values.
4. Normal flow, inline formatting, fonts, BiDi, and fragmentation foundations.
5. Positioning, floats, tables, flexbox, grid, multicolumn, and containment.
6. Backgrounds, borders, images, generated content, lists, and form controls.
7. Stacking contexts, clipping, masks, filters, blend, transforms, and opacity.
8. Transitions, animations, scrolling, media/container queries, and printing.
9. Replaced/media/canvas surfaces through bounded embedded Draw IR batches.

Each slice lands only with its matching standards manifest and modern SSpec
evidence. “Full” is reached only when the pinned supported conformance manifest
has no unimplemented required behavior; raw property counts are insufficient.

## Gates

- Legacy outputs remain stable during pure refactors.
- One Draw IR schema/diff/patch/serialization path and one UiIr execution
  schema/lowering path.
- No backend handles, caches, atlases, or transient resources in Draw IR.
- No Vulkan handles, descriptors, pipelines, or fences in UiIr.
- No duplicate semantic parser/layout owner.
- Exact Simple scalar/optimized parity for deterministic operations.
- The same UiIr semantics feed Vulkan, CUDA, HIP/ROCm, Metal, DirectX, and CPU;
  no per-surface or per-backend semantic fork.
- Backend evidence distinguishes kernel/pipeline execution, presentation,
  device readback, and CPU fallback.
- Explicit cross-browser tolerance policy for fonts/antialiasing.
- `doc/06_spec` contains no executable `.spl` files.
- Generated manuals show primary flows and contain zero stubs.
- Runtime tests use pure Simple; no Rust seed substitution.

## Decision required

Feature Option A with Vulkan-first `DrawIrComposition -> UiIr` is selected.
Select NFR 1, 2, or 3 from the matching NFR options. Architecture, final
requirements, executable SSpec additions, and implementation task breakdown
follow that selection.
