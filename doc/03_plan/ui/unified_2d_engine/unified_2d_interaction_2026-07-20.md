# Unified 2D engine: interaction, scene, physics, GPU — verified assessment + plan

Date: 2026-07-20. Provenance: architecture analysis supplied by the project
owner; every factual claim source-verified this date (VERIFY-2D lane,
file:line evidence). Annotations: [C] confirmed, [R] corrected — details in
"Verified current state". Companion: next_wave_2026-07-20.md (items 1/6).

## Problem statement (verified)

Simple has many useful 2D subsystems but no coherent production-grade 2D
engine shared by GUI, web, and games. The problem is fragmentation, not
absence of code: rendering order, hit testing, event propagation, collision
events and GPU execution do not share one scene snapshot or one semantic
contract.

Subsystems and their verified paths:
- Widget hit: src/lib/common/ui/widget_hit.spl
- Browser hit/paint: src/lib/gc_async_mut/gpu/browser_engine/layout.spl
- Browser DOM/events: browser_engine/dom.spl, dom_accessors.spl, script/event_api.spl
- Scene graph: src/lib/nogc_sync_mut/engine/scene/{node,tree}.spl
- Physics core: src/lib/nogc_sync_mut/engine/physics/world2d.spl
  (+ broadphase/bvh2d.spl, collision_layers.spl, trigger.spl)
- Physics GPU: sync tier backend_gpu/gpu_solver.spl = ALL-TODO STUB; the
  full CUDA impl lives in nogc_async_mut/engine/physics/backend_gpu/
  gpu_solver.spl — a different tier, unused by the sync PhysicsWorld2D [R]
- Compositor: src/lib/gc_async_mut/gpu/engine2d/compositor.spl

## Verified current state

| Capability | Status | Evidence |
|---|---|---|
| Drawing primitives + backend selection | Strong | engine2d audit (cae7285842578) |
| Flat compositing layers | Partial — pixel layers only | compositor.spl:17-32,124-184 [C13][C14] |
| Game scene graph | Partial — no interaction metadata; full parent-chain walk per query, all-node scan + insertion sort per z traversal | tree.spl:20-54,161-195 [C7][C8] |
| GUI hit testing | Basic — last-rect-wins, direct widget-state mutation (ui_hover/ui_pressed/checked/ui_focus/scroll_offset), no event path | widget_hit.spl:33-38,68-150 [C1] |
| GUI bounds | Half-open [l,r)x[t,b) | widget_hit.spl:21-23 [C2] |
| Browser hit testing | Reverse child order; INCLUSIVE right/bottom edges (conflicts with GUI half-open) | layout.spl:144-149,124 [C3][C4] |
| Browser z_index | Field exists; painter draws document order, hit path ignores z — no stacking contexts | dom.spl:28, layout.spl:77-96,134-150 [C5] |
| Event propagation | Listener flags stored (capture/bubbles/cancelable/...) but event_dispatch() is TARGET-PHASE ONLY; helper ignores the capture flag | event_api.spl:67-74, dom_accessors.spl:233-241 [C6] |
| Mouse events on Engine2D objects | compositor_pick_topmost + layer_rects_overlap exist (landed e033a95fe7c) but are file-level fns, NOT exported via mod.spl; no routing | compositor.spl:191-215 [R-C15] |
| Transparent click-through | Missing — pixel alpha (render skip) conflated with input transparency | compositor + draw_image alpha skip |
| Pointer capture / drag routing | Missing | — |
| Collision broad phase | Present; BVH REBUILT from scratch every contact pass (>4 colliders) | world2d.spl:130-136 [C10] |
| Collision filtering/triggers | CollisionFilter/CollisionMatrix/TriggerSystem exist as modules; detect_contacts() applies NONE of them | world2d.spl:128-209, collision_layers.spl, trigger.spl [C11] |
| GPU physics | solve_contacts() = scalar inline; sync-tier GPU solver is a stub; real CUDA solver stranded in the async tier (syncs per color batch, downloads all bodies) | world2d.spl:211-213 [C9][C12-R] |
| Dirty-region rendering | Missing — full pixel scans | compositor.spl:145-183 [C14] |
| Shared GUI/web/game scene contract | Missing | — |
| add_layer z-order bug | FIXED 2026-07-20 (e033a95fe7c) | compositor.spl:109-114 [C15] |

## Required model (adopted as-is from the owner's analysis)

### Shared flattened paint key — paint order MUST equal hit order
```
PaintOrderKey:
    surface_id
    stacking_context_order
    render_layer
    z_index
    tree_order
    insertion_sequence
```
Both rendering and hit testing consume the same flattened order; otherwise
an object can appear above another while input goes below.

### Pointer policy — rendering transparency != event transparency
```
opacity: 0.0 .. 1.0           # rendering
pointer_events: PointerPolicy # interaction

enum PointerPolicy:
    Auto | None | BoundingBox | Painted | Fill | Stroke
    SelfOnly | ChildrenOnly | Translucent
```
Two independent operations: hit-test pass-through (continue to objects
below) vs event propagation (through the chosen target's ancestors).

### Hit result and pointer routing
```
struct HitTestResult:
    primary: NodeId?
    hits: [HitRecord]        # front-to-back
    ancestor_path: [NodeId]  # root-to-primary

class PointerRouter:
    captures: Dict<PointerId, NodeId>
    hover_paths: Dict<PointerId, [NodeId]>
    pressed_targets: Dict<PointerId, NodeId>
# event.capture_pointer() / release_pointer() / has_pointer_capture(...)
```
Full capture -> target -> bubble dispatch with stopPropagation,
stopImmediatePropagation, preventDefault, non-bubbling events, passive and
once-only listeners; pointer capture substitutes the hit target while
active; over/enter/out/leave/cancel/gotcapture/lostcapture events.

### Physics event integration
Persistent contact cache keyed by (collider_a, collider_b, feature_a,
feature_b); per fixed step: update BVH proxies (persistent fat-AABB tree,
NOT rebuild) -> candidate pairs -> layer/mask filters -> narrow phase once
-> update cache -> solve -> emit Enter/Stay/Exit. Never rerun narrow phase
just to construct events. CollisionEvent2D carries phase, nodes, colliders,
normal, points, penetration, impulses, is_trigger.

### CPU/GPU boundary
CPU: input normalization, capture/target/bubble dispatch, widget/default
actions, single-pointer hit test, scene flatten + dirty tracking, contact
event construction, small deterministic physics. GPU: sprite/composite,
large transform batches, culling, particles, large-grid broad phase,
optional high-count narrow phase, optional async editor ID-buffer picking.
GPU readback is async-after-complete — keep it out of the latency-critical
pointer path.

### Unified pipeline
```
RawInputNormalizer -> Immutable FrameScene (hierarchy, world transforms,
paint keys, clip chains, hit proxies, collider proxies, dirty/versions)
  -> CPU SpatialIndex -> hit stack -> PointerEventRouter
       (capture -> target -> bubble) -> default actions -> mutations
  -> PhysicsWorld -> contact events
  -> GPU RenderQueue -> DrawIR/batches
```
Shared node data via components, not fat Node2D: Interaction2D
(pointer_policy, hit_shape, focusable, enabled, listener_table),
RenderState2D (render_layer, z_index, stacking_context, opacity, clip,
blend_mode, visible), SpatialProxy2D (world_aabb, inverse_world_transform,
proxy id, geometry_version). GUI widgets, DOM nodes and game entities
convert INTO this representation instead of calling one another.

## Optimization work (verified against current code)
- Scene: cached world transforms + local/world/bounds dirty flags + subtree
  versions (tree.spl walks the full chain today [C7]); incremental
  paint-order maintenance (today: full scan + insertion sort per traversal
  [C8]); persistent dynamic AABB tree; exact shape test after broad phase.
- Rendering: dirty rects/tiles, cached static layers, clip culling,
  occlusion rejection for opaque regions, batch sort by texture/blend/
  shader/clip, instancing, persistent GPU buffers, incremental DrawIR
  deltas, per-surface damage (today: full pixel scans [C14]).
- GPU collision (later): persistent SoA buffers -> grid keys -> radix sort
  -> pair compaction -> narrow kernels -> compact results; double/triple
  buffered readback of deltas only. Avoid upload-all/sync-each/download-all
  (exactly what the stranded async-tier CUDA solver does today [C12]).

## Implementation order

Phase 0 — Correctness (1/3 DONE)
1. ~~Fix compositor double-decrement~~ DONE e033a95fe7c [C15].
2. Standardize half-open bounds [l,r)x[t,b) everywhere — browser hit test
   currently inclusive [C4] vs GUI half-open [C2]; shared-border double-hit
   off-by-ones today.
3. Paint-order-vs-hit-order conformance tests (both consume one flattened
   order). Also: export pick_topmost/layer_rects_overlap through mod.spl —
   they are file-level today [R-C15].

Phase 1 — Shared interaction core: src/lib/common/engine/interaction/
{pointer_event, event_listener, event_route, hit_proxy, hit_test,
pointer_capture}.spl — ordered hit stack, capture/target/bubble, stop +
default-prevention semantics, pointer capture, enter/leave/over/out,
transparent hit policies.

Phase 2 — FrameScene: one immutable per-frame snapshot consumed by GUI,
browser, game, WM, hit testing, accessibility, debug; render and input
threads use a coherent snapshot version.

Phase 3 — Physics integration: connect Gen-2 modules into PhysicsWorld2D —
persistent BVH, filters, contact cache, trigger events, typed collision
events, query filters, scalar/SIMD/backend dispatch. PREREQ DECISION:
single-owner tier for the GPU solver (real impl currently stranded in
nogc_async_mut while the world lives in nogc_sync_mut [C12]).

Phase 4 — GPU offload: rendering, transform update, culling, particles,
tile-map compaction, large broad phase. Input routing stays on host.

Phase 5 — Cross-surface conformance: one scene corpus for GUI, browser and
game (topmost wins; pointer-events:none passes through; capture before
target; bubble after; stopPropagation blocks ancestors;
stopImmediatePropagation blocks later listeners; capture continues outside
bounds; clipped/invisible unhittable; opacity-0+Auto hittable;
opacity-0+None passes; reorder changes paint AND hit; trigger
Enter->Stay->Exit; masks reject pairs).

## First deliverable slice (no GPU collision)
1. Correct compositor ordering (done) + exported picker API.
2. HitProxy2D + ordered hit_stack().
3. PointerEvent2D.
4. Capture/target/bubble routing.
5. PointerPolicy.
6. Adapters for common/ui, browser DOM, Node2D.
7. Cross-surface event conformance tests.

## >> Verdict

The fragmentation diagnosis is ACCURATE: 13/15 claims verified verbatim
against source; the two corrections sharpen rather than weaken it — the
"GPU physics exists but is not the active path" claim understated the
problem (the real CUDA solver is stranded in a different memory tier from
the world that should call it), and the one capability this campaign added
(topmost picking) is still not a public API, confirming "no exported
engine capability" in spirit.

VERDICT: ADOPT the architecture and the first deliverable slice as
written, with these coordinator constraints:
1. Phase-0 items 2-3 land FIRST and alone (bounds standardization is a
   behavior change at shared borders — needs its own conformance tests
   before the interaction core builds on it).
2. The interaction core must be written landmine-clean for the
   freestanding lane from day one (no for-in-text, snapshot-to-locals
   across calls, no anon tuple returns, explicit construction-site field
   init) — it will eventually run in-guest, and this campaign filed 12
   codegen bugs proving what happens otherwise.
3. Conformance tests ship with bin/simple-run probe mirrors until the
   test-daemon wall falls (tracked; next_wave #9) — spec files alone are
   currently unrunnable.
4. Phase 3 blocks on the tier-ownership decision for the GPU solver;
   Phase 4+ blocks on next_wave #6 (backend coverage) reaching Vulkan/
   lavapipe device tests.
5. The slice supersedes next_wave item #1 (WM mouse routing): route WM
   pointer events through the NEW interaction core rather than wiring a
   one-off path to compositor_pick_topmost first.
Priority: the first slice is the highest-leverage 2D work in the repo —
it converts three divergent hit/event semantics into one contract and
unblocks every interactive feature (drag, resize, modal, canvas, games)
at once.
