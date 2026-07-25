# Simple Web, GUI, WM, GPU offloading, DrawIR optimization, and 3D physics — verified architecture review + plan

Date: 2026-07-20. Provenance: architecture review supplied by the project
owner; every load-bearing claim source-verified this date (VERIFY-3D lane,
file:line evidence). Annotations: [C] confirmed, [R] corrected. Companion:
unified_2d_interaction_2026-07-20.md (the 2D interaction core plan — Phase 1
here and Phase 1 there are THE SAME work; see Verdict item 2 for the
file-layout reconciliation).

## Overall assessment (adopted)

The central choice is correct and stays: GUI / Web / WM / Game UI lower
through their own semantic owners into DrawIR, executed by Engine2D over
CPU/SIMD/Vulkan/Metal/host-GPU. No public WebIR display list (repo decision
2026-07-14 stands). The gap is not rendering direction but retained state,
incremental update, unified events, and the 3D physics solver.

Maturity: Engine2D 8.5, DrawIR 8 (not retained/patched in production), Web 7
(whole-document cache), GUI widgets 7, WM 8, events 5 (seven divergent
models), 2D physics 7.5 (features unwired), 3D physics 5.5 (3D narrow phase
feeds a 2D solver), GPU offload 6 (frame-oriented, no retention).

## Verified current state

| Claim | Status | Evidence |
|---|---|---|
| Host compositor: damage is metadata, not incremental compositing — full recomposite + full blit on any damage | CONFIRMED | host_compositor_core.spl:496-501,800-829 ("full recomposite on any damage; partial/rect-level recomposition is deferred") [C20] |
| SimpleOS skips render when scene/taskbar revisions unchanged (scanout retains last frame) | CONFIRMED | src/os/desktop/shell.spl:863-868 [C21] |
| Host-GPU path transfers full composition + full image resources per call, full framebuffer readback per frame; no retained textures/scenes | CONFIRMED | host_gpu_ivshmem.spl:207-234; engine2d_wm_frame_executor.spl:98,166,174 [C22] |
| Input parity: host winit delivers move/all-buttons/wheel/key/focus/resize/scale; SimpleOS shared WM dispatch decodes LEFT-DOWN ONLY (button_code==1→"left" else "none"; kind==1→"down" else "none") | CONFIRMED | winit_sffi_events.rs:20-29, winit_sffi_input.rs:93-97 vs shell.spl:1017-1022 [C23] |
| Browser mouse translation drops middle+right buttons (fall through to nil) | CONFIRMED | src/app/ui.browser/event_bridge.spl:72-90 [C24] |
| Web caching is whole-document: `html == last_html` → reuse pixels, else full re-parse/style/layout; no retained WebLayoutSnapshot | CONFIRMED | simple_web_engine2d_renderer.spl:69-76 [C25] |
| DrawIR diff is O(N·M) (nested linear `_draw_ir_find_command` per command) and emits a REPORT, not an applicable patch | CONFIRMED | draw_ir_diff.spl:37-42,219-262,276-286 [C26] |
| DrawIrCommand lacks parent/property-tree info | CORRECTED — it HAS `parent_id` (draw_ir.spl:83) and an absolute `clip_rect` (:80). Real gaps: no transform/effect/scroll references, clip is a baked rect not a clip-tree node id | draw_ir.spl:68-86 [R-C27] |
| 3D world foundations real: SoA bodies, quaternion rot, 3-axis ang-vel, force/torque, fixed timestep, sphere+box narrow phase, backend field | CONFIRMED | world3d.spl, data/solver_body3d.spl:9-39,184-186 [C28] |
| CRITICAL: 3D contacts reduced to 2D — narrow phase yields point/normal xyz but constraint storage takes x/y only (z dropped at the add call); solver updates only vel x/y + ang-vel z; position solve x/y only; single tangent | CONFIRMED | collision3d.spl:7-16 vs world3d.spl:132-140,183-256,258-277; data/constraint.spl:6-20 [C29] |
| 3D broad phase missing: all-pairs O(N²); no aabb3d/dynamic_bvh3d/pair_manager3d files exist | CONFIRMED | world3d.spl:117-142; broadphase/ has only bvh2d + pair_manager (2D) [C30] |
| Capsule in enum, unreachable (collide_3d handles sphere/box only; no add_capsule_collider) | CONFIRMED | world3d.spl:14-17,144-175 [C31] |
| No manifolds/warm start: one contact per pair; constraints.clear() every sub-step | CONFIRMED | world3d.spl:113,118,130 [C32] |
| No buffered begin/stay/end events: CollisionEvent3D has no phase field and is referenced only by the STALE parallel world | CONFIRMED | types3d.spl:65-77 [C33] |
| CCD primitives exist (2D circle sweeps) but are never called by world3d | CONFIRMED | ccd.spl; zero refs in world3d.spl [C34] |
| query3d.spl is stale Gen-1: indexes `world.bodies[i]`/`world.internal_bodies` — fields the ACTIVE world does not have | CONFIRMED | query3d.spl:33-38,93-98 vs world3d.spl:38-47 [C35] |
| Backend selection is not dispatch: active_backend written once, never read; solve always scalar inline | CONFIRMED | world3d.spl:40,54,177-181 [C36] |

Verification bonus finding: a stale Gen-1 parallel 3D world lives at
`physics/simple/world3d.spl` (+ simple/query3d.spl) — the only consumer of
CollisionEvent3D. It must be quarantined/deleted as part of the query
rebuild, or agents will keep "fixing" the dead copy.

## Adopted models (from the owner's review, unmodified)

- **FrameScene**: subsystems keep authoritative mutable state (DOM, widget
  tree, WM state, game scene, physics, accessibility); a shared IMMUTABLE
  revisioned projection (stable ids, parent paths, transform/clip/effect/
  scroll trees, paint order, hit proxies, damage) feeds both rendering and
  hit testing. DrawIR stays a rendering representation, never app state.
- **RawPointerEvent**: one platform-independent raw input struct (sequence,
  timestamp, device/pointer id + kind, kind Move/Down/Up/Cancel/Wheel/
  Enter/Leave, x/y, deltas, button/buttons, pressure/tilt zeroed on PS/2,
  modifiers) — identical contract host and SimpleOS.
- **RoutedEvent + phases**: capture → target → bubble → default-action;
  stopPropagation / stopImmediatePropagation / preventDefault semantics;
  pointer capture substitutes the hit target until release; PointerPolicy
  separates visual opacity from event transparency (incl. Translucent
  hit-and-continue). WM routes content input onward (chrome first, then
  transform to surface-local and forward to the surface owner's hit test);
  wheel targets the deepest scrollable ancestor, not the window.
- **Events stay CPU-authoritative**: GPU assists only with mass culling/
  spatial queries/painted hit maps; the "GPU event offloading" that exists
  is correctly CPU-dispatch + GPU-render + receipt correlation — the missing
  piece is incremental rendering after the callback, not GPU callbacks.
- **Retained web engine**: WebLayoutSnapshot (indexed nodes, parent/child/
  sibling arrays, match/style/intrinsic/layout hashes, property-tree ids,
  dirty bitsets) + layered caches (token → DOM subtree → selector-match →
  computed-style → intrinsic → layout subtree → shaping → glyph atlas →
  paint chunk → raster tile → composited layer), each entry with explicit
  dependency revisions. A text edit invalidates its node/run/line-box/
  ancestor-size/chunk — never the document.
- **DrawIrPatch**: stable id→index/parent/chunk/bounds maps (O(N) diff);
  patch ops Insert/Remove/UpdateGeometry/UpdateStyle/UpdateText/
  UpdateResource/Reorder/SetTransform/SetClip/SetEffect with base/target
  revisions + damage rects; executor applies on revision match, rejects and
  requests a full snapshot on mismatch. Property trees (transform/clip/
  effect/scroll) referenced by id from commands instead of baked state.
- **Rendering optimization ladder**: paint chunks → raster tiles (256/512,
  content+raster revisions, scroll reuse, eviction) → opaque-region
  front-to-back occlusion → state-sorted batching/instancing within safe
  paint-order boundaries → persistent GPU buffers → frames in flight →
  direct presentation (readback reserved for screenshots/tests/debug).
- **Host-GPU persistent protocol**: HELLO/QUERY_CAPABILITIES;
  CREATE/UPDATE/UPDATE_REGION/RELEASE_RESOURCE with generational ids
  (index+generation; Texture/GlyphAtlas/WindowSurface/Buffers/DrawScene/
  RasterTile); CREATE_DRAW_SCENE/APPLY_DRAW_PATCH/DESTROY;
  SET_SURFACE_DAMAGE; SUBMIT/PRESENT; REQUEST_READBACK/FRAME_COMPLETED.
  Window move = UpdateTransform, not re-upload+full readback. Asynchronous
  submission/upload/completion rings, 2-3 frames in flight.
- **GPU job scheduler** (beyond DrawIR): jobs (render, raster, BVH update,
  physics broadphase/solve, particles, cloth, skinning, image/glyph,
  custom) with dependencies/reads/writes/fences, backend preference +
  fallback policy; scheduler weighs work size, transfer, readback, queue
  occupancy, latency, determinism, residency; small jobs stay CPU.
- **3D physics repair chain**: ContactConstraint3DSoA (normal/point/two
  tangents xyz, penetration, restitution/friction, three lambdas, feature
  ids); full impulse math (ra/rb cross terms, effective mass
  K = mA⁻¹+mB⁻¹+n·((Ia⁻¹(ra×n))×ra)+n·((Ib⁻¹(rb×n))×rb), accumulated
  clamped lambda, two-tangent friction); persistent dynamic BVH3D with fat
  AABBs + pair cache; manifolds (≤4 points, feature-id matched) + warm
  start; buffered Begin/Stay/End/Hit + sensor events consumed after step();
  CCD hybrid (discrete default, swept/TOI for bullet-flagged); Gen-2 query
  API over SolverBodyStore3D/DynamicBvh3D with QueryFilter; public API
  (set/apply/wake/filter fns, generational handles — no raw SoA mutation);
  REAL backend dispatch (match active_backend → pipeline, GPU falls back to
  CPU); no GPU solver until the CPU solver is correct AND deterministic.
- **GPU physics boundaries**: GPU = AABB/BVH, pair gen, batched narrow
  phase, large-island solve, particles/cloth, batched queries; CPU =
  mutation, event publication, callbacks, small islands, input-latency
  queries, deterministic fallback. Download compact moved-body/event lists,
  never whole body state.

## Roadmap (phases renumbered against verified state)

Phase 0 — correctness blockers: ~~compositor ordering~~ (DONE e033a95fe7c);
web render determinism; ContactConstraint3DSoA + z linear impulses + full
3-axis angular impulses; persistent manifolds; buffered 3D contact events;
replace stale Gen-1 queries (and quarantine physics/simple/ Gen-1 world).

Phase 1 — unified input/event core: SAME work as
unified_2d_interaction Phase 1. Canonical home:
`src/lib/common/engine/interaction/` (this supersedes the
`common/ui/input/` layout named in the owner's review — one dir, one core;
raw_input_event/pointer_state/default_action/gesture_arena layer into that
dir as they land). Then migrate winit, SimpleOS PS/2, InputBackend, WM,
widgets, browser DOM, game input. Near-term parity quick wins (independent
of the core, verified defects): SimpleOS decode beyond left-down [C23],
browser middle/right buttons [C24].

Phase 2 — FrameScene (stable identity, parent paths, paint order, property
trees, hit proxies, accessibility projection, damage).

Phase 3 — retained web engine (snapshot, selector/style caches, subtree
layout invalidation, shaping cache, paint chunks, parent/stacking ids,
image+iframe lowering completion).

Phase 4 — incremental DrawIR (id maps, O(N) diff, DrawIrPatch, damage
bounds, persistent executor DrawScene, apply + snapshot recovery).

Phase 5 — persistent GPU rendering (generational resources, persistent
window surfaces + glyph atlases, raster tiles, frames in flight, partial
damage execution, occlusion, instancing, direct presentation).

Phase 6 — 3D broadphase/collision completion (BVH3D, pair manager, layers/
masks, sensors, capsule, OBB, manifold gen, shape casts, CCD, sleeping/
islands, character controller). Shape order: sphere → AABB → capsule → OBB
→ compound → convex hull → static mesh → heightfield; dynamic colliders
stay convex.

Phase 7 — GPU physics (broadphase, batched narrow phase, graph coloring,
large-island solve, compact readback, deterministic CPU verification).

## First deliverable slice (10 items, adopted)

1. Unified RawPointerEvent. 2. Host/SimpleOS input parity. 3. Pointer
capture. 4. Capture/target/bubble/default-action router. 5. WM-to-content
forwarding. 6. Shared hit proxies. 7. O(N) DrawIR patch generation.
8. Persistent per-window GPU surfaces. 9. True ContactConstraint3DSoA.
10. Buffered contact begin/stay/end events.

## >> Verdict

The review is ACCURATE: 16/17 claims verified verbatim at file:line; the
one correction (DrawIrCommand already carries parent_id + a baked clip
rect [R-C27]) narrows Phase-4 scope — the work is property-tree
REFERENCES and patch application, not re-adding parentage. The 3D-physics
diagnosis is the most severe confirmed defect in the engine tree: the
solver is structurally 2D behind a 3D API, so any z-aligned stack or
collision is detected but cannot resolve. Verification also surfaced a
hazard the review missed: the stale Gen-1 world (physics/simple/) and
query3d.spl still compile-adjacent to the active world and WILL absorb
misdirected fixes.

VERDICT: ADOPT the review, its models, and the 10-item slice, with these
coordinator constraints:
1. Phase-1 module home is `src/lib/common/engine/interaction/` (already
   in flight from the companion plan); the review's `common/ui/input/`
   layout is superseded — no second interaction dir.
2. Slice items 3-6 are the companion plan's slice — do not double-build.
   Items 1-2 (RawPointerEvent + parity) and the [C23]/[C24] quick wins can
   proceed in parallel with it.
3. Slice item 9 starts as CPU-only and must land with the stale-Gen-1
   quarantine (Phase-0 item: queries) in the same campaign, else the two
   worlds diverge further. Determinism gate before ANY GPU solver work
   (the review's own rule — enforced).
4. Item 7 (DrawIR patch) must not change DrawIrCommand semantics for
   existing consumers: id maps + patch generation are additive, the diff
   REPORT stays for its current users until patch application is proven.
5. Item 8 (persistent GPU surfaces) is host-side-first: resource-revision
   retention in the ivshmem path can be built and unit-proven without QEMU;
   the in-guest proof rides the existing OVMF evidence gate, serialized
   with the other QEMU lanes.
6. All new code landmine-clean for the freestanding lane (campaign rules:
   no for-in-text, snapshot fields to locals across calls, no anon tuple
   returns cross-module, explicit construction-site field init) + probe
   mirrors until the test-daemon wall falls.
Priority order within this doc: 3D constraint correctness (item 9-10) and
input parity ([C23]/[C24]) first — both are user-visible correctness; then
DrawIR patch (item 7) as the enabler for every retention phase above it.
