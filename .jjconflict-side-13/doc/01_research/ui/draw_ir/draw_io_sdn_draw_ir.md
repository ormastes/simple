<!-- codex-research -->
# Draw.io-compatible SDN Draw IR — Research

**Date:** 2026-06-06
**Feature:** `draw_io_sdn_draw_ir`
**Status:** Reconciling external proposal against existing Draw IR v1 baseline

## Summary

A proposal asks for a tab-indented SDN "Draw IR" that is (1) HTML/CSS box-tree
first, (2) Draw.io / `mxGraph` graph-compatible second, (3) a debug/test
inspection format usable across GUI, web render, 2D renderer, and window
manager, and (4) zero/near-zero release overhead.

The key research finding is that **Simple already has a typed Draw IR v1**
(`src/lib/common/ui/draw_ir.spl`, schema `simple-draw-ir-v1`). It is the common
draw boundary the proposal asks for, but it is currently **box-only** (`rect` /
`text` commands), it has **no SDN serialization**, **no graph/edge concepts**,
and **no Draw.io interop**. So this is not a greenfield build — it is an
extension of an existing contract. This doc maps the proposal's 7 priorities to
what already exists, what is partial, and what is genuinely new, and records the
constraints the existing implementation imposes.

## Existing Reuse Points

### Draw IR contract (already the canonical boundary)

- `src/lib/common/ui/draw_ir.spl` — schema `simple-draw-ir-v1`. Owns:
  - `DrawIrCommand` (`kind` = `rect` | `text`, `component_id`, `x/y/width/height`,
    `color: u32`, `text_value`)
  - `DrawIrEmbeddingConfig` (`surface_id`, `component_id`, `x/y/width/height`,
    `layer`, `opacity_milli`, `clip: bool`)
  - `DrawIrSourceInfo` (`source_kind`, `source_id`, `html_tag`, `html_node_id`,
    `css_selector`, `css_class`, `style_key`, `style_revision`)
  - `DrawIrBatch` (schema, `batch_id`, `backend_target`, source, embedding,
    `commands`)
  - `DrawIrComposition` (ordered `batches`, `scene_key`)
  - `DrawIrEventTargetContext` — hit/route resolution for an input against a
    composition (already does stable-ID matching + stale-scene rejection)
  - `Simple2dDrawIrPlan` / `Simple2dDrawIrCompositionPlan` — cpu/gpu/auto
    backend selection with fallback reasons
- Source kinds already enumerated: `manual`, `gui_ast`, `html_ast`, `wm_scene`.
  **Three of the proposal's four surfaces are already modeled as source kinds.**

### Surface projections into Draw IR

- `src/lib/common/ui/window_scene_draw_ir.spl` —
  `shared_wm_scene_draw_ir_composition()` already projects the WM scene
  (desktop → chrome → windows) into ordered batches by z-index, with per-window
  opacity, titlebar, shadow, and clip. This is a working `wm_scene` producer.
- `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` — advanced Draw IR
  executor with CPU fallback (rect/text raster + pixel readback). This is the
  consumer side.
- HTML source plumbing exists in `DrawIrSourceInfo` (`html_tag`, `html_node_id`,
  `css_selector`, `css_class`) feeding from
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`.

### SDN substrate

- `src/lib/common/ui/parse/sdn.spl`, `parse/sdn_tree.spl` — tab-indented SDN
  readers, but **input-only** (SDN UI definition → HTML / tree). There is **no
  generic struct→SDN reflection encoder** in the repo; every SDN writer
  (`package/manifest.spl`, `database/core.spl`, `replay/trace_format.spl`, …)
  hand-rolls its emit. A `draw_ir → sdn` writer must therefore be written by
  hand like the others — it does not fall out for free.
- `doc/04_architecture/format/note_sdn_index.md` — SDN format reference.

### Shared UI test contract

- `doc/04_architecture/ui/shared_ui_contract.md` — Protocol v1. §2 "Out of
  Scope" and §7 "Assertion Contract" **explicitly exclude** CSS/browser layout
  assertions, rendered pixel output, and absolute position. §10 makes any
  semantic change a **version bump**, not an additive change.
- `src/lib/nogc_sync_mut/ui_test/client.spl` — `UITestClient` (semantic:
  click/type/drag/focus/enabled/selected).

## Proposal → Current Impl Delta (the 7 priorities)

| # | Proposal priority | Status today | Notes |
|---|-------------------|--------------|-------|
| 1 | `DrawNode` / `DrawEdge` / `DrawSnapshot` model | **Partial** | `DrawIrCommand`/`DrawIrBatch`/`DrawIrComposition` cover the box/node + snapshot roles. No `DrawEdge`, no per-node `border_rect`/`content_rect`/`hit_rect`/`computed_style`/`geometry` as typed fields. Current command is flat `x/y/w/h + color`. |
| 2 | SDN writer/reader (`draw_ir ↔ sdn`) | **Greenfield** | No serializer exists. Hand-written emit + parse needed, tab-indented, matching the proposal grammar. |
| 3 | Draw.io XML importer/exporter (`mxCell`/`mxGeometry`/style string) | **Greenfield** | No `mxGraph`/`mxCell`/`mxGeometry` references anywhere in the repo. Field mapping is fully specified in the proposal. |
| 4 | `/api/test/draw-ir` endpoint | **Greenfield + gated** | Must be **protocol v2 / opt-in**, never a v1 edit (see Constraints). `/api/test/*` plumbing exists in `src/app/ui.test_api/handler.spl`. |
| 5 | `expect_draw` test assertions | **Greenfield + gated** | Same v2 gate. Layer over `UITestClient`, do not change v1 semantic assertions. |
| 6 | Migrate pure-Simple API tests first | **Process** | Constraint, not code: do not migrate native-backend-dependent tests. |
| 7 | Visual diff (border/color/text-bounds) | **Greenfield/later** | Adjacent prior art in `doc/01_research/ui/tui/harden_tui_gui_layout_comparison.md`. |

## Current Gaps Before This Feature

1. Draw IR commands are box-only (`rect`/`text`). No edge/path/image/port/group
   command kinds, so Draw.io graph shapes have no home in the typed model yet.
2. No rich box geometry: a node has one rect (`x/y/width/height`). The proposal
   wants `layout_rect` / `border_rect` / `content_rect` / `hit_rect` and a clip
   rect. `DrawIrEmbeddingConfig.clip` is a bool with no rect.
3. No computed-style capture. `DrawIrSourceInfo` carries `css_selector` /
   `css_class` / `style_key` (provenance) but not resolved values
   (border-radius, padding, display, z-index) for assertion.
4. No serialization in or out of SDN, and no Draw.io interop.
5. No inspection endpoint or `expect_draw` matcher, and the v1 shared contract
   forbids exactly the layout/position assertions this feature introduces.
6. No debug-overhead gating: Draw IR is always constructed where used. The
   proposal wants compile-flag + runtime-flag gating so release builds pay
   near-zero cost and never stringify typed style on the hot path.

## Constraints From Existing Implementation

### Layout/CSS/position assertions are a v2 contract, not an additive change

`shared_ui_contract.md` §2/§7/§10: pixel fidelity, CSS/layout, and absolute
position are out of scope for Protocol v1, and semantic changes require a
version bump. Therefore `/api/test/draw-ir`, `expect_draw`, `hit_rect`, and
`geometry` assertions MUST ship as a **Protocol v2 / optional Draw-IR
extension**, advertised via a capability flag and a bumped
`X-UI-Protocol-Version`. They must never silently edit the v1 endpoints or v1
assertion table. Existing semantic tests (exists / text / focus / click) stay
v1 and unchanged.

### Extend the existing Draw IR, do not fork a second model

The canonical internal model must remain `DrawIr*` in
`src/lib/common/ui/draw_ir.spl`. Per the proposal's own "best design decision",
SDN/Draw.io are interchange skins over a `DrawSnapshot`, not the source of
truth — and the source of truth already exists. New command kinds and geometry
fields are **additive struct/field growth** on `DrawIrCommand` /
`DrawIrBatch`, plus a new optional `DrawEdge` command kind, not a parallel
`DrawNode` hierarchy. `schema` bumps to `simple-draw-ir-v2` when the wire shape
grows.

### Reuse the existing source/event substrate

`DrawIrSourceInfo` (provenance) and `DrawIrEventTargetContext` (hit/route
resolution with stable IDs + stale-scene rejection) already implement the
"stable IDs + hit-test region" debug concept. Computed style and hit rects
should enrich these, not replace them.

### Simple-language adaptation of the proposal sketch

The proposal's struct/`#if` sketch is C++ and must be expressed in Simple:
`struct` with no `;`, `[T]` arrays (not `SmallVec`), generics with `<>` not
`[]`, no preprocessor — debug gating is an `env`/build flag read plus a
typed-style-stringify-on-demand path, not `#if SIMPLE_DRAW_IR`. SDN is the
config/interchange format (no JSON/YAML).

## Recommended Local Architecture

Grow the existing boundary in additive layers, keep each surface a producer of
the same composition:

1. **Model growth (v2 schema).** Add command kinds (`edge`, `path`, `image`,
   `group`, `port`) and optional geometry fields (`border_rect`,
   `content_rect`, `hit_rect`, `clip_rect`) + an optional `computed_style` map
   to `DrawIrCommand`. Add `DrawEdge` (source/target/routing/waypoints/style).
   Keep `rect`/`text` v1-compatible; default new fields so v1 producers still
   validate.
2. **SDN skin.** `draw_ir_to_sdn(composition) -> text` and
   `sdn_to_draw_ir(text) -> DrawIrComposition` in a new
   `src/lib/common/ui/draw_ir_sdn.spl`, tab-indented, matching the proposal
   grammar (`draw_ir v1` / `meta` / `cell` / `box` / `geometry` / `point`).
3. **Draw.io skin.** `draw_ir_to_mxgraph` / `mxgraph_to_draw_ir` mapping
   `mxCell.id↔id`, `parent↔parent`, `vertex=1↔box`, `edge=1↔DrawEdge`,
   `mxGeometry↔geometry`, `style="a=b;"↔style map`. Canonical model stays
   `DrawSnapshot`/`DrawIrComposition`, never raw `mxGraphModel`.
4. **Inspection endpoint (v2, gated).** `/api/test/draw-ir`,
   `?id=`, `/diff`, `/layout?id=` in `app.ui.test_api`, behind a capability flag
   and bumped protocol version.
5. **`expect_draw` matcher (v2, gated).** Layer over `UITestClient`; tolerance
   + `contains` semantics as in the proposal migration samples.
6. **Overhead gating.** Build/runtime flag (`--draw-ir=off|summary|full|diff`)
   so capture and SDN stringify are skipped in release; store typed style,
   stringify only on export.

## Files Likely Touched by the Implementation

- `src/lib/common/ui/draw_ir.spl` (additive v2 fields + `DrawEdge`)
- `src/lib/common/ui/draw_ir_sdn.spl` (new — SDN writer/reader)
- `src/lib/common/ui/draw_ir_drawio.spl` (new — mxGraph importer/exporter)
- `src/lib/common/ui/window_scene_draw_ir.spl` (emit new geometry/style)
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  (emit computed style + box rects into `html_ast` source)
- `src/app/ui.test_api/handler.spl` (v2 `/api/test/draw-ir*` routes)
- `src/lib/nogc_sync_mut/ui_test/client.spl` (+ `expect_draw` helper)
- `doc/04_architecture/ui/shared_ui_contract.md` (record Protocol v2 extension)
- `test/01_unit/lib/common/ui/draw_ir_sdn_spec.spl`,
  `draw_ir_drawio_spec.spl` (new specs)

## Local Recommendation

Treat the existing `draw_ir.spl` as the source of truth and ship the proposal as
**additive v2 growth + two interchange skins (SDN, Draw.io) + a gated v2
inspection protocol**. Land the model + SDN skin first (smallest, fully
in-Simple, testable without a browser), then Draw.io interop, then the gated
endpoint/matcher, then visual diff. Do not migrate native-backend-dependent
tests, and never edit the v1 assertion table.

## Concrete Follow-on Interface Direction

1. **HTML/CSS-box-first, Draw.io-second.** Preserve Draw.io fields on the wire
   but keep computed-style + box rects as the canonical richer model, since GUI
   correctness needs intrinsic size / hit region / clip / z-order that a graph
   model lacks.
2. **Stringify-on-demand style.** Keep style typed in the model; emit the
   `style="a=b;c=d;"` string only at SDN/Draw.io export to protect the render
   hot path (the zero-overhead requirement).
3. **One snapshot vocabulary.** SDN and Draw.io are adapters that materialize
   into `DrawIrComposition`; do not let either become a second source of truth.
4. **Diff as a later channel.** Border/color/text-bounds diff reuses the
   `harden_tui_gui_layout_comparison` prior art and the composition's stable IDs.
