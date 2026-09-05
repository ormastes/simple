# Unified Packed UI Scene — one DrawIR-v3 arena for WM, GUI and Web

Status: research (local). Supersedes the earlier "add nominal GuiIR and WebIR
display-list types" proposal.

## Revised conclusion

**Do not add separate nominal `GuiIR` and `WebIR` display-list types, and do not
cast them to DrawIR.** Make WM, GUI and Web implement one *private* packed-scene
producer interface and write into the same retained DrawIR-v3 arena. "GuiIR" and
"WebIR" may exist as conceptual or module-private *views* over the same
`UiSceneSlice`, never as separately allocated command structures.

```
WM
  ├─ emits background directly
  ├─ asks GUI producer for window chrome
  ├─ asks GUI producer for global menubar and taskbar
  └─ asks each window content producer
       ├─ GUI producer
       ├─ Web producer
       └─ external-surface producer

All producers
  → same private count/reserve/emit interface
  → same DrawIR-v3 scene arena
  → same Prepared2D batch plan
  → Engine2D
  → Vulkan / Metal / CUDA / CPU
```

Not `WM IR → copy to GuiIR → copy to WebIR → copy to DrawIR`, but *WM / GUI / Web
semantic owners each write different portions of one shared DrawIR-v3 scene*.

Event flow is the reverse of composition:

```
component ID + generation
  ← DrawIR hit shape
  ← GUI/Web/WM owner table
  ← exact semantic owner
```

---

## 1. What the current repository plans establish

### 1.1 DrawIR v3 is already the intended packed hot representation

`DrawIrV3Scene` is deliberately flat and GPU-oriented: fixed-width
`DrawIrV3Command`; numeric component and parent IDs; no text keys in render-hot
records; no nested dynamic arrays; geometry, paint, text, resources, paths,
clips, transforms, hit shapes and provenance as flat side-table columns;
variable-length payloads as spans.

The 2026-08-01 native-layout plan establishes Vulkan-canonical values and
layouts: Vulkan consumes v3 without enum or record conversion, while Metal and
DirectX translate through an accessor seam. Intended final backend shape is
persistent descriptors and command buffers, direct SSBO upload, O(batch)
dispatch, zero mid-frame resource allocation after warm-up. S1, S2 and initial
S5 sizing exist; direct Vulkan SFFI and the complete persistent batch executor
remain unfinished.

### 1.2 Production still uses DrawIR v2

The reconciliation plan states production remains on `simple-draw-ir-v2`. v3 has
a flat schema and a CPU-reference emitter, but no production GUI/Web producer and
no Engine2D v3 executor. Introducing GuiIR and WebIR now would create a third and
fourth representation before the second is production-ready.

### 1.3 Active plans already reject separate WebIR/GuiIR display lists

The Web optimization plan says not to introduce `WebIR` or `WebIrDocument`; Web
semantic/layout state stays private and lowers into the shared DrawIR display
list. The unified 2D plan makes the same call for GUI, and identifies the old
second GUI command representation as dead duplication.

Where earlier research says "WebRender IR" as a conceptual stage, that wording
must now mean *the Web renderer's private retained semantic/layout state*, not a
second shared display-list schema.

Consistent with modern practice: Chromium moved to a global display list plus
property trees rather than independently rendered layer trees; Firefox transforms
layout output into a self-contained WebRender display list with arena-backed
display items used for painting and hit testing.

---

## 2. Gaps in the current v3 optimization design

Directionally correct, not yet sufficient for WM → GUI/Web → DrawIR.

### 2.1 The A–E emitter is exact-size but not persistent-allocation-free

`draw_ir_v3_emit.spl` implements: **A** count records → **B** exclusive prefix
scan → **C** verify capacity → **D** write at exact offsets → **E** cull and
construct batches. After the scan, output lengths do not change — the correct
deterministic no-growth algorithm.

But each invocation still creates and fills new arrays; in-tree comments note it
uses push loops to build exact-sized buffers because the common tier lacks a
fixed-capacity primitive. So: no reallocation *during* emission, but not zero
allocation *between* frames. Production needs a session-owned arena whose buffers
are allocated once and reused across scene generations.

### 2.2 The emitter does not populate the full v3 schema

Populated: commands, geometry, paint, text runs, paths. Constructed **empty**:
resource tables, clip tables, transform tables, hit-shape tables, provenance
tables. It writes `NO_ID` for image-resource, clip, transform and hit-shape
references, and batch keys are returned outside `DrawIrV3Scene`.

Insufficient for: background images and motion surfaces; Web images; window-local
transforms; scrolling via parent transforms; clipping; hit testing and reverse
event routing; rendering provenance; cross-process or external surfaces.

### 2.3 The submission port cannot guarantee zero-copy

The frozen `PackedDrawPort` accepts `submit_scene(scene: DrawIrV3Scene)` **by
value** and does not receive the external batch plan. `DrawIrV3Scene` contains
multiple value-semantic arrays; the existing optimization audit already flags
value-array copy-in/copy-out as a material cost; batch keys live outside the
scene; a native Vulkan backend needs stable column addresses and lengths, not an
owning aggregate copied across the call.

The C0 port is frozen — do not edit in place. Add a versioned port based on an
arena lease or stable object handle.

### 2.4 Capacity byte accounting is incomplete

The backend stride profile defines sizes for command, geometry, paint, text,
glyph, resource, path, clip and transform records, but the total-byte function
adds only a subset (nodes, layout records, glyphs, batches, commands, path
points, patch operations). For a genuine one-time reservation the capacity
contract must cover: commands, geometry, paint, text runs, glyphs, resources,
path spans and points, clips, transforms, hit shapes, provenance edges, prepared
batches, component owners, action bindings, dirty ranges, scan scratch, backend
preprocess scratch.

Where a formal bound exists (`geometry_count <= command_count`) derive it;
otherwise the bound is explicit and overflow stays **fail-closed**.

---

## 3. Updated architecture: one hidden packed UI scene

### 3.1 Semantic state stays separate

WM owns windows, focus, z-order, active app, taskbar, background, workspaces.
GUI owns widgets, constraints, focus, accessibility, commands, layout. Web owns
DOM, CSS rules, computed style, layout boxes, text fragments, scripts. Merging
these into one struct would produce a large sparse union and damage both
modularity and performance. What must be identical is the *render-production
interface* and the *final packed storage*.

### 3.2 One shared private producer interface

Internal contract; **not** exported through the public UI facade. Simple has no
inheritance — this is a trait, composed in, per `.claude/rules/language.md`:

```simple
trait UiPackedProducer:
    # Pass A: report exact required rows for every destination table.
    fn count(snapshot_id: u64, mut counts: UiSceneCounts)

    # Pass D: write directly into pre-reserved ranges.
    fn emit(
        snapshot_id: u64,
        ranges: UiSceneRanges,
        mut draw: DrawIrV3Writer,
        mut owners: UiOwnerWriter,
        mut actions: UiActionWriter
    )
```

Every producer returns the same slice type:

```simple
struct UiSceneSlice:
    scene_slot: u32
    scene_generation: u32
    root_component_id: u32
    ranges: UiSceneRanges
```

Producers returning `UiSceneSlice`: WM background, GUI window-chrome, GUI
taskbar, GUI global-menubar, GUI application content, Web document,
external/native surface.

If the design docs keep the words, define them conceptually only:
`GuiIR = UiSceneSlice produced by GUI`, `WebIR = UiSceneSlice produced by Web`.
They are **not** separate nominal command structs.

### 3.3 GUI containing Web creates no intermediate copy

A GUI WebView node invokes the Web producer during the *same* count/emit:

```
GUI count → count widgets, then call Web producer count for the WebView child
global prefix scan → reserve exact ranges once
GUI emit  → emit widgets, then call Web producer emit into its assigned ranges
```

The Web root component takes the GUI WebView component as its cross-layer parent:
`WM window → GUI content root → GUI WebView → Web document root → DOM/layout
descendants`. No child `DrawIrComposition` is flattened by allocating a new
array; the child is assigned ranges in the same scene arena.

### 3.4 Same storage, typed views, no casting

```
UiSceneLease
├─ DrawIrV3SceneView
├─ UiOwnerTableView
├─ UiActionTableView
├─ Prepared2DView
└─ DirtyRangeView
```

`DrawIrV3SceneView` is a non-owning view over the same v3 columns. The CPU oracle
keeps using the owning `DrawIrV3Scene` value type; native backends use the view.

Views beat casting because casting would depend on hidden object headers,
field-order ABI assumptions, value-array copies, interpreter/native/Wasm layout
differences, and future compiler representation changes. Both views reference the
same physical storage, so the result is still zero-copy.

### 3.5 Versioned scene-reference port

Keep the frozen v1 port for compatibility and tests. Add additively:

```simple
struct PackedSceneRef:
    object_slot: u32
    object_generation: u32
    scene_id: u32
    scene_generation: u32

trait PackedDrawPortV2:
    fn capabilities() -> u32
    fn submit_scene_ref(
        scene: PackedSceneRef,
        prepared: Prepared2DRef,
        dirty: DirtyRangeRef
    ) -> DrawIrV3SubmitReceipt
    fn present(scene_generation: u32) -> bool
```

The slot+generation model already matches the repo's MDSOC+/Object-VM design for
stable hot references without raw relocatable pointers.

---

## 4. Hierarchical DrawIR removes recalculation

The v3 schema admits `GROUP` and `PORT`, but production execution semantics are
incomplete — the reconciliation plan records that *schema admission is not
rendering support*. Give them precise semantics.

### 4.1 GROUP — inherited state

Parent component, local transform, clip, opacity, visibility, descendant
component range. Use for windows, title bars, window content, scroll containers,
taskbar, global menubar, popup menus, GUI panels, Web documents and embedded
frames. Children use local coordinates.

| Change | Work |
|---|---|
| Move a window | patch one window-group transform |
| Scroll a document | patch one scroll-group transform and clip |
| Animate minimize | patch group transform and opacity |
| Hide a menu | patch group visibility |
| Move a WebView | patch the GUI WebView group; Web scene unchanged |

The CPU v3 executor must define transform, clip and opacity inheritance first;
Prepared2D then resolves the hierarchy into backend-ready flat state.

### 4.2 PORT — content not emitted into the current scene

Native/external application surface, cross-process app scene, video or motion
wallpaper surface, GPU-resident media surface, independently committed child
scene. A `PORT` command references a registered resource or scene handle, **not**
copied pixels. Same-process GUI and Web normally emit into the common arena;
`PORT` is for isolation or ownership boundaries.

---

## 5. WM composition including background

```
Desktop root
├─ Background                       WM direct producer
├─ Desktop widgets                  GUI producer
├─ Window group 0
│  ├─ shadow/chrome                 GUI producer
│  └─ content ├─ GUI slice ├─ Web slice └─ PORT/external surface
├─ Window group 1
├─ Global menubar                   GUI shell producer
├─ Taskbar / dock                   GUI shell producer
├─ Popup and notification overlays  GUI shell producer
└─ Cursor/debug overlays
```

### 5.1 Background needs no widget overhead

Background is shell state and usually has no event semantics — emit directly.
**Color**: one retained full-desktop `RECT`, no hit shape. **Image**: one retained
`IMAGE` command; resource table entry holds the retained image resource;
fit/placement via transform and clip. The image provider runs only when the
source changes, the viewport changes in a way affecting fit, or the resource
generation changes. **Motion/video**: one `PORT` or IMAGE-like media command;
resource/surface generation changes per frame while scene geometry stays
retained — update the media resource generation or surface binding rather than
rebuilding WM DrawIR.

A failed provider preserves the current **loud, fail-closed** marker behaviour —
never silently substitute a different background.

---

## 6. macOS-style global menubar

Today `command_lane` is only a top-screen geometry and dispatch region (clock,
right-side icons, a generic lane target) — not an active-application menu system.
Retain the rectangle as a compatibility field; rename the semantic to
**`global_menubar`**.

### 6.1 Ownership — one WM/shell-owned top-screen surface

Left: active application menus (application menu, File, Edit, View, Window,
app-defined). Right: shell status area (system status items, notifications,
network/power/audio, clock). **Not embedded in each window.**

Matches macOS: the menu bar occupies the top of the screen, the foremost app owns
the displayed main menu, availability changes with the active scene and focused
view hierarchy, and untargeted actions route through the responder chain.

### 6.2 Application menu snapshot

```simple
struct AppMenuSnapshot:
    app_id: u32
    app_generation: u32
    menu_revision: u32
    focused_owner_id: u32
    # Flat side-table ranges, not nested arrays in the hot path.
    root_start: u32
    root_count: u32
    item_start: u32
    item_count: u32
    action_start: u32
    action_count: u32
```

Menu item storage holds numeric IDs: `menu_item_id`, `parent_item_id`,
`label_string_id`, `action_id`, `flags`, `shortcut_id`, `enabled`, `checked`,
submenu range. The convenient API may still expose nested `Menu`/`MenuItem`
objects or a Simple DSL, compiled into the flat snapshot only when the menu
revision changes.

### 6.3 Active app vs key window

Track `active_app_id`, `key_window_id`, `focused_owner_id` separately. An app can
stay active while its key window changes, and Cut/Copy/Paste enablement depends
on the focused GUI or Web control, not merely the app or window.

### 6.4 Focus switch

Update `active_app_id` → select cached `AppMenuSnapshot` → patch **only** the
global-menubar scene segment → preserve background, taskbar and window-content
segments → recompute menu text only when the selected snapshot/revision differs.
With no active application, show a shell-default menu.

### 6.5 Menu actions carry no function pointer

```simple
struct MenuActionBinding:
    app_id: u32
    app_generation: u32
    menu_revision: u32
    action_id: u32
    default_target_owner_id: u32
```

Dispatch validates all generations before delivery — the same model serves local
apps, process-isolated apps and SimpleOS IPC.

---

## 7. Reverse event routing

Use existing v3 component and parent identities, never string lookups.

```
Pointer/key event
  → Engine2D or GPU hit query
  → hit_shape.component_id + component_generation
  → UiOwnerTable[component_id]
  → semantic producer and semantic node
  → producer-local capture/target/bubble
  → optional host/default action
  → WM action only when the owner chain reaches WM
```

```simple
struct UiOwnerRecord:
    producer_kind: u16       # WM, GUI, WEB, EXTERNAL
    semantic_id: u32
    semantic_generation: u32
    parent_owner_id: u32
    action_binding_id: u32
    event_policy: u16
```

**Nested WebView**: DrawIR Web button → Web DOM button → DOM ancestors → Web
document root → GUI WebView host → GUI window-content root → WM window.
"Exactly backward" means the *ownership chain* is the reverse of composition — it
does **not** mean every event mechanically executes every layer. Web performs DOM
capture/target/bubble; the GUI WebView receives a translated host event or
default-action result; WM receives only relevant focus, window, drag or shell
actions.

**Menubar**: menubar DrawIR item → shell menubar widget → `MenuActionBinding` →
active application → focused GUI/Web responder → application command handler.
Keyboard shortcuts use the same binding and need no synthetic pointer hit.

**Window chrome**: close button DrawIR → GUI button owner → window-chrome action
adapter → WM close-window action. The GUI layer never mutates `WindowManager`
directly.

---

## 8. Allocation and the "free-calculation" target

Literal zero calculation is unrealistic — synchronization, damage selection,
visibility checks and command submission remain. The meaningful target:

> No semantic recomputation, no structural allocation, no string processing, no
> enum conversion and no per-primitive backend object creation in the
> unchanged-frame hot path.

### 8.1 Session-owned scene arena

Allocated once at renderer/session creation: commands, geometry, paint, text
runs, glyphs, resources, path spans/points, clips, transforms, hit shapes,
provenance, owner records, action bindings, prepared batches, dirty ranges,
count/scan scratch, backend preprocess scratch.

Front/back generations — **front** immutable, currently rendered and hit-tested;
**back** receives validated patches for the next generation; **swap** only after
backend completion/fence permits reuse. A lower-memory SimpleOS lane may use one
buffer with an explicit completion barrier, preserving the same logical contract.

### 8.2 Capacity extension (additive, do not mutate the frozen manifest)

```simple
struct UiSceneCapacityExtensionV1:
    max_geometry_rows: u32
    max_paint_rows: u32
    max_text_runs: u32
    max_resources: u32
    max_path_spans: u32
    max_clips: u32
    max_transforms: u32
    max_hit_shapes: u32
    max_provenance_edges: u32
    max_owner_records: u32
    max_action_bindings: u32
    max_prepared_batches: u32
```

Rule stands: count → scan → verify → emit exactly or reject explicitly. **No
automatic growth, no silent truncation.**

### 8.3 Retained component ranges

Segments: background, global-menubar, taskbar, per-window chrome, per-window
content. Each carries `semantic_revision`, `layout_revision`, `paint_revision`,
`resource_revision`, `transform_revision`, `visibility_revision`.

| Change | Required work |
|---|---|
| Nothing changed | no producer count/emit; no scene upload |
| Window moved | patch one group transform and damage bounds |
| Window focus changed | patch chrome paint and menubar selection |
| Document scrolled | patch scroll-group transform/clip |
| One button state changed | patch its paint row |
| Menu opened | enable/unhide one overlay group |
| Background unchanged | no background work |
| Wallpaper image changed | patch one resource and background command |
| Motion wallpaper frame | update resource/surface generation only |
| Web text changed | re-layout affected subtree, patch its ranges |

### 8.4 Overflow strategy

Count the new exact requirement → try another free block inside the already
reserved session arena → if still insufficient, reject the incremental update
with an **overflow receipt** → schedule an explicit scene replan outside the
render-hot path. **Never silently grow active arrays while Vulkan is reading
them.**

---

## 9. Prepared2D — canonical scene separate from backend calculation

Rather than adding backend fields to the frozen scene, define a derived sidecar:

```simple
struct Prepared2DBatch:
    first_command: u32
    command_count: u32
    target_surface_id: u32
    pipeline_id: u32
    resource_set_id: u32
    resolved_clip_id: u32
    resolved_transform_id: u32
    flags: u32
```

A complete Prepared2D package carries the batch table, resolved group/property
state, render-task dependencies, resource binding table, dirty upload byte
ranges, damage rectangles, visible-command ranges and a backend
capability/profile key.

Pipeline: retained hierarchical DrawIR v3 → resolve changed GROUP state →
visibility and damage → construct/reuse Prepared2D batches → backend execution.

Cache key: scene generation, backend identity, backend capability generation,
pipeline/resource generation, viewport generation. Unchanged scene and backend
state reuse the same plan.

---

## 10. Vulkan-native execution

The existing plan is correct but must consume the scene *lease* and prepared
sidecar rather than an owning scene value.

```
UiSceneArena → canonical Vulkan-compatible columns → upload only dirty byte
ranges → SSBOs / resource tables → persistent descriptors → one dispatch/draw per
Prepared2D batch → one frame completion signal → direct present
```

Persistent state — **per-device**: pipelines, descriptor layouts,
sampler/resource registries. **Per-frame-in-flight**: command pool, command
buffer, descriptor pool/cache, staging/upload region, completion fence or
timeline value. **Per-scene**: device buffers, resource bindings, Prepared2D
batches, dirty upload map.

Consistent with Khronos guidance: reuse or reset command pools instead of
repeatedly allocating/freeing command buffers, keep command-buffer counts
reasonable, maintain per-frame resource pools and descriptor caches; static
descriptor sets and buffer-based resource access are established paths.

**Do not make optional Vulkan features the baseline.** Descriptor heaps/buffers,
device-generated commands, indirect command buffers and persistent kernels are
later capability tiers selected through the existing capability contract:

- **Tier 0** — persistent classic descriptors + SSBO batch execution
- **Tier 1** — indirect dispatch/draw
- **Tier 2** — descriptor heap/buffer, device-generated commands, persistent
  kernel/work graph where available

---

## 11. Minimum-change refactoring plan

**Phase 0 — reconcile and freeze the design.** Add
`doc/05_design/ui/unified_packed_ui_scene.md`; update
`draw_ir_backend_native_refactor_plan.md`, `webir_drawir_optimization.md`,
`draw_ir_web_renderer_reconciliation_2026-07-31.md`,
`rendering_inside_rendering.md`, and the WM internal-window/global-shell design.
Record: (1) no public GuiIR or WebIR; (2) one private `UiPackedProducer`; (3) one
physical DrawIR-v3 scene arena; (4) semantic state stays producer-private; (5)
GROUP and PORT semantics are mandatory; (6) scene references replace by-value
submission in the native path; (7) the global menubar is one shell surface bound
to the active app. **No runtime behaviour changes.**

**Phase 1 — v2/v3 bridge and CPU v3 executor.** Leave producers unchanged:
`WM/GUI/Web → existing DrawIrComposition v2 → typed v2→v3 adapter → CPU v3
executor`. Complete RECT, TEXT, IMAGE/resources, PATH, GROUP, PORT, clips,
transforms, hit shapes, provenance. **Gate:** `v2 CPU pixels == v3 CPU pixels`
across WM, GUI and Web corpora. Allows v3/backend development without rewriting
the Web parser, CSS cascade, GUI layout or public APIs.

**Phase 2 — complete the v3 emission contract.** An emitter version that counts
and writes every v3 table; owner/action sidecars; Prepared2D; complete
capacity-extension byte accounting; explicit overflow receipts; stable component
ID allocator. Keep the A–E emitter as the reference oracle.

**Phase 3 — arena lease and port v2.** Likely new modules:

```
common/ui/ui_scene_counts.spl
common/ui/ui_scene_slice.spl
common/ui/ui_scene_owner_table.spl
common/ui/ui_scene_capacity_extension.spl
common/ui/draw_ir_v3_submission.spl
common/ui/draw_ir_v3_ports_v2.spl
nogc_sync_mut/ui/ui_scene_arena.spl
nogc_sync_mut/ui/draw_ir_v3_native_writer.spl
```

One-time allocation; front/back generation; stable object handle; no scene-array
copies at submission; v1 compatibility adapter for tests. **Gate:** after
warm-up — render-scene allocations 0, descriptor allocations 0, command-buffer
allocations 0.

**Phase 4 — shared producer interface.** Adapt producers one at a time: Panel2D,
widget tree, WM chrome, Web final paint lowering, nested WebView/iframe, external
surfaces. Old public functions remain adapters (`widget_tree_to_draw_ir`,
`simple_web_layout_render_html_draw_ir`) for compatibility and the v2 oracle.

**Phase 5 — WM background and global menubar.** Reuse `BackgroundSpec` and
providers, `TaskbarModel`, `SharedWmScene`, the current command-lane rectangle,
existing focus/window state. Add `AppMenuSnapshot`, `AppMenuRegistry`,
`GlobalMenuBarState`, `MenuActionBinding`, global-menubar GUI producer.
`SharedWmChrome.command_lane` is retained as a legacy alias for global-menubar
geometry. **Gate:** exactly one top-screen menubar; switching active apps changes
left menus; right status items persist; menu action reaches active app/focused
control; no menu subtree duplicated per window; background, windows and taskbar
unchanged by menu switching.

**Phase 6 — reverse event routing.** Populate `hit_shape_id`, hit-shape component
IDs, component generations, parent chains, owner records, action bindings.
Migrate window chrome, taskbar, global menubar, GUI widgets, Web content,
wheel/scroll, keyboard shortcuts. **Gate:** same component identity across paint,
hit, event route, and accessibility/source provenance.

**Phase 7 — retained segments and dirty patches.** Component range table;
per-segment revisions; transform-only patches; resource-only patches; dirty GPU
byte ranges; visibility and occlusion culling; retained Prepared2D. **Gates:**
unchanged frame → 0 commands rewritten, 0 bytes uploaded; window move → O(1)
transform rows; scroll → O(1) transform/clip rows; active-app switch → only
menubar segment changed.

**Phase 8 — Vulkan S3/S4 completion.** Direct packed Vulkan creation records;
direct native Vulkan SFFI; persistent resources; SSBO/range batch execution;
dirty-range upload; direct presentation; explicit fallback receipt;
physical-device exact parity and counters. **Do not remove the CPU/v2 oracle.**

**Phase 9 — production cutover.** After parity and hardware evidence: production
is direct WM/GUI/Web packed producer → DrawIR v3; compatibility keeps the v2
adapter, software pixel oracle and direct legacy pixel path. Only then classify
or remove duplicated direct WM/Web pixel painters.

---

## 12. Likely refactoring scope

Engineering estimates, **not measured counts**.

| Milestone | Production files | Specs | Lines |
|---|---|---|---|
| First functional (shared interface, menubar, WM background, v2-backed) | 10–16 | 8–12 | 2,000–4,000 |
| Packed v3 production (emitter, CPU executor, arena lease, port, owner/action, direct producers) | 20–30 | 15–25 | 5,000–10,000 |
| Vulkan-native (SFFI, persistent resources, SSBO batching, dirty upload, evidence) | 8–15 runtime/backend/shader | — | 2,000–5,000 + shaders |

First milestone requires no public application API change, no Web
parser/CSS/layout rewrite, no frozen v3 schema edit. The Vulkan milestone is
largely the already-planned S3/S4 work, not a new architectural rewrite.

---

## Final design decisions

1. DrawIR v3 is the one hot render IR.
2. WM, GUI and Web retain different semantic models.
3. All three implement the same private count → reserve → emit interface.
4. All three return the same `UiSceneSlice`.
5. GUI and Web write directly into the same arena; no conversion or cast between them.
6. Owner/action/provenance data lives in side tables, not in every hot command.
7. Background is a WM root primitive/resource, not necessarily a widget.
8. Window chrome, taskbar and global menubar are GUI shell widgets.
9. The menubar is one top-screen shell surface populated from the active application's menu snapshot.
10. Events walk the reverse component-owner chain using numeric IDs and generations.
11. GROUP transforms/clips make window movement, scrolling and animation small patches, not subtree rebuilds.
12. Prepared2D carries cached batch/backend calculation outside the frozen DrawIR schema.
13. The native path submits stable scene references, not a by-value scene aggregate.
14. After warm-up, unchanged frames perform no scene allocation, no producer emission and no GPU upload.
15. Vulkan consumes canonical v3 columns directly and executes O(batch), while v2 and CPU remain the correctness oracle.

---

## Convention notes (repo rules applied to this research)

- **No inheritance** — `UiPackedProducer` and `PackedDrawPortV2` are traits,
  composed in; see `.claude/rules/language.md`.
- **Generics use `<>`, not `[]`.**
- **Tier placement** — pure/immutable scene vocabulary in `src/lib/common/ui/`;
  the mutable session-owned arena and native writer in
  `src/lib/nogc_sync_mut/ui/`, matching `.claude/rules/structure.md`.
- **MDSOC+** — slot+generation handles align with the Object-VM design; userland
  services use MDSOC outer + ECS business layer.
- **Fail-closed** — overflow rejects with a receipt; a failed background provider
  keeps the loud marker. Never silently truncate or substitute.
- **All code in `.spl`.** Struct/trait sketches above are illustrative shapes, not
  final signatures.
- Sizing figures in §12 are estimates and are labelled as such; they are not
  measured and must not be cited as counts.
