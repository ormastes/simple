# Claim validation — `unified_packed_ui_scene.md` research

Status: validation report (read-only lane, 2026-08-05). Every factual claim the
research makes about the current tree was checked against source. Verdicts:
**12 CONFIRMED, 0 REFUTED, 0 PARTIALLY-TRUE** (two confirmed claims carry
nuances, noted inline). Downstream design/plan lanes may build on these claims.

Vendored paths excluded. All greps pinned to `/usr/bin/grep` and anchored.

## Claim table

| # | Claim | Verdict | Evidence |
|---|-------|---------|----------|
| 1 | `DrawIrV3Scene` is flat/GPU-oriented: fixed-width command, numeric IDs, no text keys, no nested arrays; nine flat side tables; spans for variable payloads | **CONFIRMED** | `src/lib/common/ui/draw_ir_v3.spl:10-23` states the invariant verbatim ("render-hot structures contain no text keys and no nested dynamic arrays"); `DrawIrV3Command` :79-94 is all u16/u32 (numeric `component_id`, `parent_id`, side-table ids only); flat SoA tables geometry/paint/text/resources/paths/clips/transforms/hit-shapes/provenance :102-183; glyph and path payloads are (start,count) spans :116-119, :140-147. Sole text field is the host-side `schema` banner :285-287, documented as never uploaded :20-23 |
| 2 | `draw_ir_v3_emit.spl` implements A–E (count → exclusive scan → verify → exact-offset write → cull/batch); after the scan output lengths do not change | **CONFIRMED** | `src/lib/common/ui/draw_ir_v3_emit.spl:1-23` (kernel list + invariant "After the scan, no output array changes length"); Kernel A `draw_ir_v3_count_records` :306, B `draw_ir_v3_exclusive_scan` :363, C `draw_ir_v3_verify_capacity` :418, D `draw_ir_v3_emit` :442 (one-time exact sizing :453-488, indexed writes :490-577), E `draw_ir_v3_compact_batch` :689. The no-growth invariant is made observable by `draw_ir_v3_emit_matches_plan` :623-641 |
| 3 | Emitter populates commands/geometry/paint/text-runs/paths; constructs EMPTY resource/clip/transform/hit-shape/provenance tables; writes `NO_ID` for image-resource/clip/transform/hit-shape refs | **CONFIRMED** | Scene construction `draw_ir_v3_emit.spl:579-616`: populated commands/geometry/paint/text_runs/path_points :584-611 vs `draw_ir_v3_empty_resource_table()` :605, `..._empty_clip_table()` :612, `..._empty_transform_table()` :613, `..._empty_hit_shape_table()` :614, `..._empty_provenance_table()` :615. Command constructor passes `DRAW_IR_V3_NO_ID` for image_resource :549, clip :551, transform :552, hit_shape :553 |
| 4 | Batch keys are returned outside `DrawIrV3Scene` | **CONFIRMED** | `DrawIrV3EmitResult.batch_keys` sidecar `draw_ir_v3_emit.spl:437-440`; comment :435-436 "deliberately not a scene field: the frozen v3 contract is not extended here"; item-level `batch_key` marked "Host-side batching key. Not part of the frozen scene" :97-98 |
| 5 | Push loops build exact-sized buffers because the common tier lacks a fixed-capacity primitive; no realloc during emission, but not zero allocation between frames | **CONFIRMED** | In-tree comment `draw_ir_v3_emit.spl:227-231`: "`src/lib/common/` has no `with_capacity` / `filled` primitive … the one-time sizing pass is a fill loop"; `_v3e_zeros_*` push loops :233-271. Every `draw_ir_v3_emit` invocation allocates fresh columns :454-488 — there is no persistent arena anywhere in the file |
| 6 | `PackedDrawPort.submit_scene(scene: DrawIrV3Scene)` by value, no batch plan, and the port is frozen | **CONFIRMED** (freeze is convention-only — see nuance) | `src/lib/common/ui/draw_ir_v3_ports.spl:85-90`: `fn submit_scene(scene: DrawIrV3Scene) -> DrawIrV3SubmitReceipt` — an owning value-type aggregate of value-semantic arrays, no `Prepared2D`/batch parameter (batch keys live in the emit sidecar, claim 4). **What "frozen" is enforced by:** the file header only — :32-34 "After C0 is merged, this file is read-only until an explicit schema-version change (isolation rule 3)", citing `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` §9/§12 I1. No script in `scripts/check/` and no `.claude/rules/` entry references `draw_ir_v3_ports`; there is **no mechanical guard** — the freeze is documentation/process, not tooling |
| 7 | Total-byte function covers only a subset (nodes, layout records, glyphs, batches, commands, path points, patch ops) and omits several v3 tables | **CONFIRMED** | `src/lib/common/ui/gpu_web_capacity_strides.spl`: `GpuWebBackendStrideProfile` :104-119 defines strides for command, geometry, paint, text_run, glyph, resource, path_point, clip, transform (plus node/layout_box/batch/patch/fragment/line_box); but `gpu_web_capacity_bytes` :182-194 sums ONLY nodes, layout_boxes, fragments, line_boxes, glyphs, draw_batches, draw_commands, path_points, patch_operations — the geometry, paint, text_run, resource, clip and transform strides are defined and **never added** |
| 8 | Production still uses DrawIR v2 (`simple-draw-ir-v2`); v3 has no production GUI/Web producer and no Engine2D v3 executor | **CONFIRMED** (verified in code, not just the plan) | Plan statement: `doc/03_plan/ui/unified_2d_engine/draw_ir_web_renderer_reconciliation_2026-07-31.md:4-6` "Production still uses `simple-draw-ir-v2`; the additive [v3] … have no production producer or Engine2D executor", table row :29. Code reachability: v2 schema `src/lib/common/ui/draw_ir.spl:6`; Engine2D emits/checks only v2 (`src/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_adv.spl:30`, `host_gpu_event_queue.spl:515`); GUI producer imports v2 `common.ui.draw_ir` (`src/lib/common/ui/widget_draw_ir.spl:26`), Web producer likewise (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:6`). Repo-wide, the only non-comment `DrawIrV3` reference outside `src/lib/common/ui/` is an import of `draw_ir_v3_backend_enums` (`src/lib/nogc_sync_mut/engine/render/vulkan_backend3d.spl:63`) — enum values, not the scene; the other four matches (placement_contracts/schema.spl:19, parse_types.spl:9, dom_arena_types.spl:15, descriptor_table.spl:12) are comments citing v3 as a convention precedent |
| 9 | GROUP and PORT are schema-admitted but have no complete production execution semantics | **CONFIRMED** | `DRAW_IR_V3_KIND_GROUP`/`_PORT` defined `draw_ir_v3.spl:42-43` and exported :893 — and those are the **only** occurrences of either constant in all of `src/` (no producer constructs them, no executor matches them; zero hits in `draw_ir_v3_oracle.spl` and `draw_ir_v3_execution_route.spl`). The reconciliation plan states it explicitly: :85-87 "Use **schema-admitted** for RECT/TEXT/EDGE/PATH/IMAGE/GROUP/PORT … Do not count schema constants as rendering", :30 "executor handles RECT/TEXT/IMAGE" |
| 10 | `command_lane` is only a top-screen geometry/dispatch region (clock, right icons, generic lane target), not an active-application menu system | **CONFIRMED** | `SharedWmChrome.command_lane: SharedWmRect` `src/lib/common/ui/window_scene.spl:279-281`; built as full-width strip at y=0 :611; hit area resolves to right icons / clock / generic lane (`_wm_command_lane_hit_area` :816, dispatch :859-865 returning `command_lane_icon`/`command_lane_clock`/`command_lane`); dispatch handling `src/lib/common/ui/wm_runtime_dispatch.spl:115-148,210`. The string "menu" occurs **zero** times in `window_scene.spl`, `window_scene_draw_ir.spl`, and `wm_runtime_dispatch.spl` |
| 11 | WM has color/image/motion background provider concepts; the WM DrawIR path imports a shared background resolver | **CONFIRMED** | `BackgroundSpec` `window_scene.spl:62`, color constructor :81, `trait BackgroundImageProvider` :115 (+ registration :125), `trait MotionBackgroundSource` :154 (+ registration :174); shared resolver `shared_wm_scene_resolve_background` :260 with loud fail-closed refusals :239-250; imported by the WM DrawIR path `src/lib/common/ui/window_scene_draw_ir.spl:50` and called :473, :1613; OS-side providers `src/os/compositor/background_image_provider.spl`, `src/os/compositor/background_motion_provider.spl` |
| 12 | Web optimization plan says NOT to introduce `WebIR`/`WebIrDocument`; unified 2D plan says GUI/Web emit DrawIR directly and calls the old second GUI command representation dead duplication | **CONFIRMED** | `doc/03_plan/ui/webir_drawir_optimization.md:116` "**Decision: do not add a `WebIR`/`WebIrDocument` type or a second display-list**"; `doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md:111` "…DIRECTLY (no WebIR/GuiIR exists; `widget_draw_cmds.spl` is a dead second GUI [representation]…". The value-array copy cost the research cites (§2.3) is also real: same doc :122 "copy-in/copy-out on value-type arrays is O(N²) per frame → pass `mut cmds`". Note: `src/lib/common/ui/widget_draw_cmds.spl` still exists in-tree — declared dead, not yet deleted |

## Named-but-nonexistent entities

The research is disciplined here: every type it relies on as *existing today*
was found in source (verified: `DrawIrV3Scene`, `DrawIrV3Command`,
`PackedDrawPort`, `DrawIrV3SubmitReceipt`, `SharedWmScene`,
`SharedWmChrome.command_lane`, `TaskbarModel`, `BackgroundSpec`,
`DrawIrComposition`, `Panel2D`, `widget_tree_to_draw_ir`,
`simple_web_layout_render_html_draw_ir`, and all four plan docs it names).
The following are named in the research and exist **nowhere in `src/`** — all
are explicitly framed as proposals, but a downstream plan must treat every one
as net-new work, not reuse:

- Producer interface: `UiPackedProducer`, `UiSceneCounts`, `UiSceneRanges`,
  `UiSceneSlice`, `DrawIrV3Writer`, `UiOwnerWriter`, `UiActionWriter`
- Lease/views: `UiSceneLease`, `DrawIrV3SceneView`, `UiOwnerTableView`,
  `UiActionTableView`, `Prepared2DView`, `DirtyRangeView`, `UiSceneArena`
- Port v2: `PackedSceneRef`, `PackedDrawPortV2`, `Prepared2DRef`,
  `DirtyRangeRef`
- Capacity: `UiSceneCapacityExtensionV1`
- Menubar: `AppMenuSnapshot`, `AppMenuRegistry`, `GlobalMenuBarState`,
  `MenuActionBinding`
- Events: `UiOwnerRecord`

Two items that read as existing infrastructure but are not code:

1. **`Prepared2D`** — the intro diagram lists "same Prepared2D batch plan" as a
   shared pipeline stage. The only in-source occurrence of the token is a
   comment in `draw_ir_v3_ports.spl:10` citing plan §12 I6. There is no
   `Prepared2D*` type anywhere in `src/`; `Prepared2DBatch` (research §9) is
   new. Kernel E's `DrawIrV3Batch`/`DrawIrV3CompactResult`
   (`draw_ir_v3_emit.spl:661-673`) is the closest existing thing.
2. **`hit_shape.component_generation`** (research §7 event flow) —
   `DrawIrV3HitShapeTable` (`draw_ir_v3.spl:167-174`) carries `component_ids`
   but **no generation column**; `component_generation` exists only on
   `DrawIrV3Command` (:84). A hit query that must return id+generation needs a
   command-table join or a new column — a real (small) schema gap for Phase 6.

Minor factual note: research §1.2 says v3 tables were verified via the
reconciliation plan; the plan's claims were independently re-verified in code
here (claim 8 row) and hold.

## What this validation cannot see

- **Reachability beyond static imports.** Claims 8/9/12 were checked by
  symbol definition + reference greps and import statements, not by executing
  the render paths. This repo's `use` resolution is fail-open (an unresolved
  `use` is a warning), and modules can be registered by unrelated imports, so
  "imports v2" is strong but not runtime proof of which code a production
  session actually executes.
- **Doc claims about intent** ("Vulkan-canonical", "S3/S4 remain unfinished",
  tier plans) were checked only as far as the named plan docs stating them
  (`draw_ir_backend_native_refactor_plan.md` header: S1/S2/S5 DONE with commit
  ids, S0/spec execution DEFERRED, S3/S4/S6 open). Whether those commits'
  contents match their labels was not re-audited.
- **The frozen-port guarantee** is a comment plus plan-doc process rule; this
  validation found no hook/lint enforcing it, and cannot rule out an
  enforcement mechanism living outside `scripts/check/` and `.claude/rules/`.
- **Value-vs-reference passing cost** (claim 6 "by value") is asserted from
  language semantics (arrays/structs are value types in Simple) and the
  repo's own audit note; no measurement was taken in this lane.
- **Behavioral completeness of the A–E emitter** (byte-for-byte oracle claims)
  was not re-run; `bin/simple test` was out of scope for a read-only
  validation lane and the test harness has known false-green modes.
