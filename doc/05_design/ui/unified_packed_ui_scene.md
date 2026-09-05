# Unified Packed UI Scene — Design

Status: design (authoritative for this feature). Derived from
`doc/01_research/local/unified_packed_ui_scene.md`.
Companion execution plan: `doc/03_plan/ui/unified_packed_ui_scene_agent_lanes.md`.

## 0. Decision record

1. **No nominal `GuiIR` / `WebIR` display-list types, ever.** "GuiIR" and
   "WebIR" are permitted only as *words* meaning "the `UiSceneSlice` produced by
   GUI / by Web". They are never separately allocated command structures and are
   never cast to DrawIR.
2. **One private producer contract** (`UiPackedProducer`, a trait — no
   inheritance) implemented by WM, GUI, Web and external-surface producers.
3. **One physical DrawIR-v3 scene arena** per session. Producers write disjoint
   pre-reserved ranges of the same arena; GUI-hosting-Web assigns the Web
   producer ranges in the same arena, no intermediate copy.
4. **Semantic state stays producer-private.** WM window/focus state, GUI widget
   tree, Web DOM/CSS/layout are never merged into a shared struct.
5. **GROUP/PORT get precise executable semantics** (§4) — schema admission is
   not rendering support.
6. **Native submission is by stable reference** (`PackedSceneRef`,
   slot+generation), not by-value scene aggregates. The existing v1
   `PackedDrawPort` is **frozen — never edited in place**; v2 is additive.
7. **Fail-closed everywhere.** Overflow, under-emission, over-emission,
   unsupported clip/opacity forms, missing PORT surfaces: reject with a typed
   receipt or render the loud marker. Never silently truncate, grow, skip or
   substitute.

## 0.1 Assumptions to be confirmed (containment per assumption)

A sibling lane is validating the research's factual claims. This design depends
on them as follows; each is contained so a wrong assumption does not invalidate
the design:

| # | Assumption (from research) | Containment if wrong |
|---|---|---|
| A1 | `draw_ir_v3_emit.spl` implements exact-size A–E (count→scan→verify→write→batch) but reallocates per invocation | We keep it untouched as the reference oracle either way. The full-schema emitter is a **new file**; if A–E is not exact-size, the new emitter still is, and the oracle role transfers to `draw_ir_v3_oracle.spl` pixel output. |
| A2 | `PackedDrawPort` (v1, `src/lib/common/ui/draw_ir_v3_ports.spl`) is frozen and takes `DrawIrV3Scene` by value | v2 is a separate new file regardless. If v1 already supports references, `PackedDrawPortV2` shrinks to the receipt/dirty-range additions; no lane edits v1 in any branch of reality. |
| A3 | GROUP/PORT are schema-admitted but have no complete production execution semantics | The group-resolver lane begins with a capability probe spec. If execution already exists, the lane becomes a conformance-spec + gap-fix lane against §4 semantics instead of a from-scratch implementation. |
| A4 | `command_lane` is only top-screen geometry + generic dispatch, not a menu system | The menubar design keeps `command_lane` as an untouched legacy geometry alias. If it carries more semantics, those are wrapped, not replaced. |
| A5 | Capacity byte accounting covers only a subset of tables | `UiSceneCapacityExtensionV1` is a sidecar struct in a new file. The frozen capacity manifest (`gpu_web_capacity_manifest.spl`) is never edited. |

## 1. Module map and tier placement

Per `.claude/rules/structure.md`: pure value vocabulary → `src/lib/common/ui/`;
session-owned mutable state and native writers → `src/lib/nogc_sync_mut/ui/`;
WM-side producers → `src/lib/nogc_async_mut/wm/` (respecting the WML001/WML002
ratchet — no new violations).

| New file (additive; no existing file edited unless listed) | Tier | Why this tier |
|---|---|---|
| `src/lib/common/ui/ui_scene_counts.spl` — `UiSceneCounts`, `UiSceneRanges`, `UiSceneTableId`, `UiSceneOverflowReceipt`, `UiSceneCapacityExtensionV1` | common | Pure value types + pure arithmetic (scan, verify). No mutation, no I/O. |
| `src/lib/common/ui/ui_scene_slice.spl` — `UiSceneSlice`, `UiPackedProducer` trait, writer traits | common | Interface vocabulary; trait defs are pure. |
| `src/lib/common/ui/ui_scene_owner_table.spl` — `UiOwnerRecord`, `MenuActionBinding`, owner-chain walk (pure) | common | Value records + pure reverse-routing walk over supplied tables. |
| `src/lib/common/ui/ui_scene_prepared2d.spl` — `Prepared2DBatch`, `Prepared2DPlan`, cache key | common | Derived value sidecar; construction is a pure function of scene + capability key. |
| `src/lib/common/ui/draw_ir_v3_group_resolve.spl` — GROUP/PORT resolver (§4) | common | Pure function: scene columns in → resolved flat state out. |
| `src/lib/common/ui/draw_ir_v3_ports_v2.spl` — `PackedSceneRef`, `PackedDrawPortV2` trait, `DrawIrV3SubmitReceipt` | common | Trait + value types only; implementations live in backend tiers. |
| `src/lib/common/ui/draw_ir_v2_to_v3.spl` — typed v2→v3 adapter | common | Pure translation of value structures. |
| `src/lib/common/ui/draw_ir_v3_emit_full.spl` — full-schema exact-size emitter (§5) | common | Pure count/scan/verify/emit over value buffers; the CPU oracle path. |
| `src/lib/nogc_sync_mut/ui/ui_scene_arena.spl` — session arena, front/back generations, lease | nogc_sync_mut | Long-lived mutable session state, allocate-once buffers. |
| `src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl` — bounds-checked cursor writers over arena ranges | nogc_sync_mut | Mutates arena storage in place. |
| `src/lib/common/ui/app_menu_snapshot.spl` — `AppMenuSnapshot`, flat menu-item storage | common | Immutable compiled snapshot; value semantics. |
| `src/lib/nogc_sync_mut/ui/app_menu_registry.spl` — `AppMenuRegistry`, `GlobalMenuBarState` | nogc_sync_mut | Mutable registry keyed by app slot+generation. |

**Read-only for every lane** (frozen or owned elsewhere): `draw_ir_v3.spl`,
`draw_ir_v3_ports.spl` (v1), `draw_ir_v3_emit.spl` (oracle), `draw_ir_v3_oracle.spl`,
`gpu_web_capacity_manifest.spl`, `gpu_web_capacity_strides.spl`,
`src/lib/nogc_async_mut/wm/host.spl` (`WmHost2d`, commit `556e6ebe042`).

## 2. Type surface (normative)

All code `.spl`; generics `<>`; traits + composition only. Field names below are
normative; widths are normative unless a lane records a measured reason to
change one (record it in this doc, additively).

### 2.1 Tables and counts

Sixteen destination tables, identified by `UiSceneTableId` (u16 enum, stable
numbering — this is a cross-module contract, append-only):

```
0 COMMANDS        1 GEOMETRY       2 PAINT          3 TEXT_RUNS
4 GLYPHS          5 RESOURCES      6 PATH_SPANS     7 PATH_POINTS
8 CLIPS           9 TRANSFORMS    10 HIT_SHAPES    11 PROVENANCE_EDGES
12 OWNER_RECORDS 13 ACTION_BINDINGS 14 PREPARED_BATCHES 15 DIRTY_RANGES
```

```simple
struct UiSceneCounts:
    # one u32 row-count per UiSceneTableId, same order
    rows: [u32; 16]

struct UiSceneRange:
    start: u32
    count: u32

struct UiSceneRanges:
    # one range per UiSceneTableId, same order
    table: [UiSceneRange; 16]
```

(If fixed-size array fields are not yet expressible in the target tier, the
fallback is 16 named `u32` / `UiSceneRange` fields with the same names as the
enum — record which form was used. Do not use a growable list here.)

### 2.2 Producer contract

```simple
trait UiPackedProducer:
    # Identity for owner records and receipts. Stable within a session.
    fn producer_kind() -> u16          # UI_PRODUCER_WM | _GUI | _WEB | _EXTERNAL
    fn producer_id() -> u32

    # Pass A: report EXACT required rows for every table for this snapshot.
    # Must be side-effect free and repeatable for the same snapshot_id.
    fn count(snapshot_id: u64, counts: UiSceneCounts) -> UiSceneCounts

    # Pass D: write into pre-reserved ranges. Must write EXACTLY the counted
    # rows per table — no fewer, no more (§5.2). A nested producer (WebView)
    # is invoked here with its sub-ranges.
    fn emit(snapshot_id: u64, ranges: UiSceneRanges,
            draw: DrawIrV3Writer, owners: UiOwnerWriter,
            actions: UiActionWriter) -> UiSceneEmitResult
```

`UiSceneEmitResult` is `Emitted(UiSceneSlice)` or
`Refused(UiSceneOverflowReceipt)` — a producer refuses rather than clamps.

```simple
struct UiSceneSlice:
    scene_slot: u32
    scene_generation: u32
    root_component_id: u32
    ranges: UiSceneRanges
```

Nesting rule (GUI hosting Web): the host's `count` calls the child's `count`
and adds the child's counts to its own; the global scan runs once; the host's
`emit` calls the child's `emit` with the child's sub-ranges carved from the
host's ranges. The child's root component takes the host component (the WebView
node) as `parent_id`. One arena, zero intermediate structures.

### 2.3 Writers (bounds-checked, deficit/surplus fail-closed)

```simple
trait DrawIrV3Writer:
    fn put_command(row: DrawIrV3Command) -> bool      # false = out of range
    fn put_geometry(row: ...) -> bool                 # …one per table…
    fn cursor(table: UiSceneTableId) -> u32
    # Verifies cursor == reserved count for EVERY table this writer covers.
    fn finish() -> UiSceneWriteVerdict                # Exact | Deficit(table,n) | Surplus(table,n)
```

`UiOwnerWriter` / `UiActionWriter` follow the same shape over tables 12/13. A
`false` return or non-`Exact` verdict aborts the generation: the back buffer is
marked invalid, the front generation is untouched, and a receipt is produced.
Under-emission is as fatal as overflow — a deficit leaves stale rows that would
render.

### 2.4 Owner and action records

```simple
struct UiOwnerRecord:
    producer_kind: u16        # WM, GUI, WEB, EXTERNAL
    event_policy: u16         # bitset: HIT_OPAQUE|HIT_TRANSPARENT|FOCUSABLE|SCROLL_TARGET|…
    semantic_id: u32          # producer-private node id
    semantic_generation: u32
    parent_owner_id: u32      # NO_ID at the WM root
    action_binding_id: u32    # NO_ID when none

struct MenuActionBinding:
    app_id: u32
    app_generation: u32
    menu_revision: u32
    action_id: u32
    default_target_owner_id: u32
```

Dispatch validates `app_generation` and `menu_revision` (and the hit shape's
`component_generation`) before delivery; any stale generation drops the event
with a routed-refusal receipt, never delivers to a recycled slot. No function
pointers anywhere in these records.

### 2.5 Prepared2D sidecar

```simple
struct Prepared2DBatch:
    first_command: u32
    command_count: u32
    target_surface_id: u32
    pipeline_id: u32
    resource_set_id: u32
    resolved_clip_id: u32
    resolved_transform_id: u32
    flags: u32                # bit 0: NEEDS_OFFSCREEN (see §4.1 opacity)

struct Prepared2DPlan:
    batches: UiSceneRange             # into PREPARED_BATCHES table
    dirty_upload: UiSceneRange        # into DIRTY_RANGES table (byte ranges)
    damage_rect_count: u32
    capability_key: u64               # backend identity+capability generation
    scene_generation: u32
```

Cache key = (scene_generation, capability_key, viewport_generation). Unchanged
key → reuse the plan bit-for-bit, zero reconstruction.

### 2.6 Versioned port (v1 stays frozen)

```simple
struct PackedSceneRef:
    object_slot: u32          # MDSOC+/Object-VM slot
    object_generation: u32
    scene_id: u32
    scene_generation: u32

trait PackedDrawPortV2:
    fn capabilities() -> u32
    fn submit_scene_ref(scene: PackedSceneRef, prepared: Prepared2DRef,
                        dirty: DirtyRangeRef) -> DrawIrV3SubmitReceipt
    fn present(scene_generation: u32) -> bool
```

`DrawIrV3SubmitReceipt` carries `accepted: bool`, `reason: u16`,
`scene_generation`, `commands_seen: u32`. Refusal reasons reuse the established
honest-refusal vocabulary: where the surface comes from the WM host seam, the
refusal is the existing `WmHost2dUnavailable` (`src/lib/nogc_async_mut/wm/host.spl`)
— do **not** invent a parallel "surface unavailable" type. Port-level reasons
(stale generation, capability mismatch, capacity) are new codes in the receipt.

### 2.7 Capacity extension (sidecar; frozen manifest untouched)

```simple
struct UiSceneCapacityExtensionV1:
    max_rows: [u32; 16]       # per UiSceneTableId, incl. scratch-backing tables
    scan_scratch_rows: u32
    backend_scratch_bytes: u32
```

Byte totals derive from `max_rows` × the existing stride profile
(`gpu_web_capacity_strides.spl`, read-only). Where a formal bound exists
(`geometry_count <= command_count`) it is derived; otherwise explicit.

## 3. Arena and generations

`UiSceneArena` (nogc_sync_mut) is allocated once at session creation from a
`UiSceneCapacityExtensionV1`. Two generations: **front** (immutable; being
rendered and hit-tested) and **back** (receives the next generation's writes).
Swap only after the backend completion signal for the front generation permits
reuse. A single-buffer low-memory mode is the same logical contract with an
explicit completion barrier before write — same types, one flag, no divergent
API. The lease:

```
UiSceneLease
├─ DrawIrV3SceneView      # non-owning views over the same v3 columns
├─ UiOwnerTableView
├─ UiActionTableView
├─ Prepared2DView
└─ DirtyRangeView
```

Views, never casts: no dependence on object headers, field-order ABI, or
engine-specific layout. The CPU oracle keeps the owning `DrawIrV3Scene` value;
native consumers use views over identical physical storage.

## 4. GROUP / PORT semantics (normative, implementable)

### 4.1 GROUP

A GROUP command carries: `parent_id`, `transform_id` (local, TRANSFORMS table),
`clip_id` (local, CLIPS table, `NO_ID` = none), `opacity` (u16, 0..65535 =
0.0..1.0), `flags` (bit 0 VISIBLE), and its descendant command range
(`first_child_command`, `child_command_count`). Descendants are **contiguous**
— the scan allocates each group subtree contiguously; the resolver rejects a
non-contiguous or overlapping child range with a receipt (fail-closed
structural check, not an assumption).

Resolution (pure pass in `draw_ir_v3_group_resolve.spl`, run only for changed
groups after the first full resolve):

- **Transform.** Children are authored in group-local coordinates.
  `world(child) = world(parent) ∘ local(group)` — parent applied after local
  (column-vector convention, matching the v3 transform table's row layout as
  the resolver lane confirms it; the composition ORDER here is normative, the
  matrix memory layout is whatever v3 already defines).
- **Clip.** Clips in v3 are axis-aligned rects in the clip's own space.
  `effective_clip(child) = intersect(effective_clip(parent), world_aabb(local_clip))`.
  If a group's accumulated world transform is not axis-preserving (rotation/
  skew) and it carries a clip, the resolver marks `NEEDS_OFFSCREEN` on the
  affected batches; an executor that cannot honor it **refuses with a receipt**
  — it never renders with the clip dropped.
- **Opacity.** `effective = parent_effective × group_opacity` (u16 multiply,
  round-to-nearest, clamp). Tier-0 semantics apply effective opacity
  per-primitive, which differs from composited group opacity exactly when
  descendants overlap. A group with opacity < 1.0 **and** the OVERLAPPING hint
  flag set gets `NEEDS_OFFSCREEN`; same refuse-don't-degrade rule.
- **Visibility.** `effective_visible = parent AND group`. An invisible group
  excludes its entire descendant range from batching, upload **and hit
  testing** (hidden UI must not eat clicks).
- **Hit testing** uses the same resolved state: a point hits a shape iff it is
  inside every effective clip on the chain and inside the shape under the
  inverse world transform. One transform truth for paint and hit.

Patch table (this is the point of GROUP — each is a 1-row patch, not a subtree
rebuild): window move → 1 transform row; scroll → 1 transform + 1 clip row;
minimize animation → transform + opacity; menu hide → visibility bit.

### 4.2 PORT

A PORT command references a registered surface handle
(`surface_id: u32`, `surface_generation: u32`) — external/native app surface,
cross-process scene, media surface. Never copied pixels. A PORT behaves as a
leaf rect for transform/clip/opacity/visibility inheritance and for hit testing
(its owner record routes to the EXTERNAL producer). Content is sampled at
execution time; a per-frame media update changes only the surface generation,
never the scene geometry. An unavailable or stale-generation surface renders
the **loud fail-closed marker** and produces a receipt — never a silent skip,
never a substituted surface. Same-process GUI and Web do **not** use PORT; they
emit into the common arena. PORT is exclusively an ownership/isolation
boundary.

## 5. Overflow contract (fail-closed state machine)

```
COUNT  → every producer reports exact rows per table (pure, repeatable)
SCAN   → one exclusive prefix scan per table assigns disjoint ranges
VERIFY → for each table: total <= capacity.max_rows[t]
         PASS → EMIT;  FAIL → UiSceneOverflowReceipt, NOTHING emitted,
                              front generation untouched
EMIT   → bounds-checked writers; finish() must be Exact per producer per table
         Deficit/Surplus/out-of-range → generation invalidated + receipt
```

```simple
struct UiSceneOverflowReceipt:
    table_id: u16
    kind: u16                 # CAPACITY | DEFICIT | SURPLUS | RANGE_VIOLATION | STRUCTURE
    required: u32
    capacity: u32
    producer_kind: u16
    producer_id: u32
    snapshot_id: u64
```

Incremental updates: count the new exact requirement → try a free block inside
the already-reserved arena → still insufficient → reject with the receipt and
schedule a full replan **outside** the render-hot path (replan may allocate a
new, larger arena between generations; the in-flight arena is never grown while
a backend reads it). **No automatic growth. No silent truncation. Ever.**

## 6. Global menubar (scoped for this design)

One WM/shell-owned top-screen surface; `command_lane` geometry retained as a
legacy alias (A4). `active_app_id`, `key_window_id`, `focused_owner_id` tracked
separately. Focus switch patches only the menubar segment via the cached
`AppMenuSnapshot` (flat side-table ranges, §2 of research — the struct is
adopted as written). The nested `Menu`/`MenuItem` convenience DSL is **deferred
until an application consumer exists** — the flat snapshot is the only v1
surface.

## 7. Frozen vs additive (hard rule)

| Frozen — no lane may edit | Additive — new files only |
|---|---|
| `draw_ir_v3_ports.spl` (v1 port) | `draw_ir_v3_ports_v2.spl` |
| `draw_ir_v3.spl` schema records | resolver, emit-full, adapter, sidecars |
| `gpu_web_capacity_manifest.spl` / `_strides.spl` | `UiSceneCapacityExtensionV1` |
| `draw_ir_v3_emit.spl` (A–E oracle) | `draw_ir_v3_emit_full.spl` |
| `draw_ir_v3_oracle.spl` | conformance specs against it |
| `wm/host.spl` (`WmHost2d`) | producers consuming it |

## 8. Explicitly speculative — do not build yet (no consumer)

- Vulkan Tier 1/2 (indirect dispatch, descriptor buffers, device-generated
  commands, persistent kernels). Tier 0 has no producer feeding it yet.
- Cross-process PORT and SimpleOS IPC menu dispatch — the generation-validated
  binding model is designed to extend there; the transport is not designed here.
- Motion/video wallpaper — depends on a media-surface registry that does not
  exist; the PORT semantics above are sufficient when it does.
- Menu DSL / nested convenience API (§6).
- Phase 8 (Vulkan S3/S4) and Phase 9 (production cutover) — sequenced after
  parity evidence; planning them in lanes now would be over-engineering.

## 9. Correctness oracles kept alive

`v2 CPU pixels == v3 CPU pixels` (via the v2→v3 adapter) is the standing gate
across WM/GUI/Web corpora; the A–E emitter and `draw_ir_v3_oracle.spl` remain
the reference; nothing in this design removes the software pixel path.
