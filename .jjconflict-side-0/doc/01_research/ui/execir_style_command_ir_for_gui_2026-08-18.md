# ExecIR-Style Command IR for GUI ("guiIR") — Applicability Analysis

Date: 2026-08-18. Lane: ANALYSIS (no product code changed).
Subject: does the ExecIR approach (`src/compiler/95.interp/execir.spl` — flat
pre-decoded i64 command arrays, pooled constants, tight dispatch loop) apply to
sequenced GUI/render command streams, and does the repo already have such an IR?

## Verdict (up front)

**The ExecIR *principles* apply strongly to GUI frames — and the repo already
has the GUI equivalent, designed and partially built: the Unified Packed UI
Scene (DrawIR-v3 packed arena).** Its design record explicitly forbids a new
nominal "GuiIR" type (`doc/05_design/ui/unified_packed_ui_scene.md` §0 item 1:
*"No nominal `GuiIR` / `WebIR` display-list types, ever"* — those words may
only mean "the `UiSceneSlice` produced by GUI/Web"). Therefore the correct
recommendation is **do not introduce a new guiIR; finish executing the existing
packed-scene lanes**, which already embody every ExecIR idea the orchestrator
asked about (flat numeric tables, encode-once/replay-per-frame via
generation-keyed caching, dirty-range re-encode, closed op set, fail-closed
capacity). A second, independent guiIR would violate that standing decision
record and duplicate five active lanes.

## 1. Survey: sequenced-command representations that already exist

The GUI stack does **not** walk object trees per frame at the backend boundary;
it already flattens to command lists at several layers:

| Layer | File(s) | Shape |
|---|---|---|
| Widget tree → flat draw list | `src/lib/common/ui/widget_draw_cmds.spl` | `[DrawCmd]` structs (kind:text, x/y/w/h:i32, color:u32) — flat but **string-kinded**, per-record struct, not packed |
| Draw IR v2 (production) | `src/lib/common/ui/draw_ir.spl`, `widget_draw_ir.spl` | `DrawIrCommand` records; command kinds and style props are **text** ("rect", key/value text pairs) — heap/string heavy |
| Draw IR v3 (typed) | `draw_ir_v3.spl`, `draw_ir_v2_to_v3.spl`, `draw_ir_v3_emit.spl` | Typed tables (commands/geometry/paint/text/resources/path/clip/transform/hit_shapes) — the ExecIR-shaped layer |
| **Packed scene arena** | `ui_scene_slice.spl` (u32/u16 ids, table cursors), `ui_scene_prepared2d.spl`, `ui_gui_packed_producer.spl`, `wm_packed_producer.spl`, `ui_web_packed_producer.spl`, `draw_ir_v3_ports*.spl` | One per-session DrawIR-v3 arena; producers (WM/GUI/Web) write disjoint pre-reserved ranges; native submission by stable reference (`PackedSceneRef`, slot+generation), never by value |
| Frame replay/caching | `ui_scene_prepared2d.spl` | `Prepared2DBatch` (first_command/command_count/pipeline/clip/transform, all u32) + `Prepared2DCacheKey` (scene_generation, capability_key, viewport_generation): *"Unchanged key → reuse the plan bit-for-bit, zero reconstruction"* |
| Dirty regions | `dirty_region.spl`, `Prepared2DPlan.dirty_upload` (byte ranges into DIRTY_RANGES table) | Partial re-encode/upload already designed in |
| game2d batching | `src/lib/nogc_sync_mut/game2d/render/draw_batcher.spl`, `sprite_batch.spl`, `engine/render/command.spl` | Sort by (z, texture_id), flush a `RenderCommandBuffer` per frame — classic command buffer |
| GPU backends | `src/lib/*/gpu/engine2d/backend_*.spl` | Consume Draw-IR batches; CPU reference + GPU kernels held to a bit-exact parity oracle (`doc/01_research/ui/rendering/cpu_gpu_dual_algorithm_research.md` §1) |
| WM text protocol | `play_wm_text_*` tooling, `wm_packed_producer.spl` | Text protocol is for *tooling/inspection*; the render path is the packed producer, not the text protocol |

So: rendering already flattens to command lists everywhere that matters. The
remaining tree-walk cost is in the **producer** step (widget layout/paint →
v2 → v3), and the packed-scene lanes exist precisely to make that step
incremental (generations + dirty ranges) instead of per-frame.

## 2. Fit analysis: where ExecIR ideas do and don't add value

ExecIR wins on: (a) encode once, execute many times; (b) numeric-heavy operands
pre-decoded into pools; (c) removing per-command enum/dict dispatch.

- **(a) Re-execution:** exactly the GUI frame pattern, and already captured —
  `Prepared2DCacheKey` reuses a plan bit-for-bit across frames when
  scene/capability/viewport generations are unchanged. ExecIR's "encode once"
  is the packed scene's "scene_generation unchanged".
- **(b) Numeric operands:** DrawIR **v2** fails this test (text command kinds,
  text style props) — it is the GUI analog of the pre-ExecIR enum-dispatch
  interpreter. **v3/packed tables pass it** (u32/u16/u64 fields throughout).
  The measured cost of the wrong shape is on record: interpreted per-pixel /
  per-element loops run **830–897 ms/frame at 720p** for scalar
  clear/read_pixels, and per-pixel FFI hops cost ~10x a single native call
  (`cpu_gpu_dual_algorithm_research.md`, measurements of 2026-07-07). That is
  the "interpreter-bound web-layout lane" problem class the orchestrator
  cited: dispatch and boxing dominate; the fix is the same as ExecIR's —
  flat pre-decoded numeric arrays consumed by a native executor.
- **(c) Dispatch overhead:** the per-command hot loop lives in the engine2d
  backends (`backend_software.spl` op switch, GPU kernels per op). With
  batches expressed as `Prepared2DBatch` ranges (first_command +
  command_count into a packed table), per-command dispatch collapses to a
  range submit — better than ExecIR's per-op while-loop, because a GUI
  backend can execute a *range* natively/GPU-side, which an interpreter
  opcode loop cannot. No fresh micro-measurement was run for this analysis
  (analysis lane; shared contended box makes single-frame timings noise);
  the 2026-07-07 numbers above are the load-bearing evidence.

## 3. The memory/unpredictability concerns, in the GUI case

The concerns raised against ExecIR for general programs largely **do not
transfer**:

- **Memory:** a general program's ExecIR is bounded by code size and register
  pressure of arbitrary functions. A GUI command buffer is bounded by *scene
  size* — commands ≈ visible primitives, known at layout time. The packed
  design goes further: capacity is a **manifest** (`gpu_web_capacity_manifest.spl`,
  frozen) with fail-closed overflow (typed receipts, never silent truncation) —
  memory is not merely predictable, it is pre-reserved and audited.
- **Unpredictability / fallback:** ExecIR must bail to `MirInterpreter` for
  anything outside its subset (calls, memory, floats, strings), so its coverage
  is unpredictable per program. The GUI op set is **closed by construction**
  (the DrawIR-v3 schema: rect/text/edge/path/image/group/port + typed tables);
  there is no open-ended fallback problem. The one analog — a backend lacking
  a capability (offscreen compositing, `UI_SCENE_PREPARED2D_FLAG_NEEDS_OFFSCREEN`)
  — is handled fail-closed by design (§0 item 7): refuse with a receipt rather
  than degrade silently. Honest residual risk: text shaping and PATH commands
  are the variable-cost ops; they are isolated in their own tables, so worst
  case is a fat table, not an unbounded interpreter escape.

## 4. Recommendation and next step

**Reject a new guiIR type; adopt the ExecIR principles by completing the
existing Unified Packed UI Scene.** Everything the sketch would contain is
already designed with authority:

- closed op set → DrawIR-v3 schema + §4 GROUP/PORT semantics;
- flat i64/u32 command arrays with pooled constants → packed arena tables +
  resource/paint tables (pooling by id);
- double-buffered command arrays → `PackedSceneRef` slot+**generation** (a new
  generation is the second buffer; the old one stays valid until release);
- dirty-region re-encode → `Prepared2DPlan.dirty_upload` byte ranges +
  `dirty_region.spl`;
- MDSOC fit → already resolved by the design's tier map (§1): pure vocabulary
  in `src/lib/common/ui/`, session-owned arena/writers in
  `src/lib/nogc_sync_mut/ui/`, WM producers in `nogc_async_mut/wm/`; the
  model/layout/style separation is untouched because producers stay
  semantic-state-private (§0 item 4).

**Next-step slice** (if the orchestrator wants motion here): the batch
*construction* lane — the pure function from a resolved v3 scene to
`Prepared2DBatch` rows + dirty ranges — is explicitly deferred in
`ui_scene_prepared2d.spl` ("the actual batch construction … is a later lane;
this file is the vocabulary only"). That is the smallest slice that turns the
per-frame widget-tree walk into encode-once/replay, and it is pure `common/`
code, testable without a backend. Cross-check lane status in
`doc/03_plan/ui/unified_packed_ui_scene_agent_lanes.md` before claiming it.

## 5. Slice landed 2026-08-18: Prepared2DBatch construction

`src/lib/common/ui/ui_scene_prepared2d_build.spl` implements the deferred
construction lane: exact encode-time capacity (`ui_scene_prepared2d_batch_capacity`),
pure construction (`ui_scene_prepared2d_build`, batch boundary = kind-derived
pipeline + clip_id + transform_id), and generation-keyed reuse
(`Prepared2DBuildCache`, `build_count` as rebuild proof). Spec:
`test/01_unit/lib/ui/ui_scene_prepared2d_build_spec.spl`.

TODO(prepared2d): remainder of the lane — dirty_upload byte-range production
(hook into `dirty_region.spl`), damage_rect_count, paint/resource-aware
pipeline specialization, and NEEDS_OFFSCREEN flag derivation from group
opacity/rotated-clip analysis.
