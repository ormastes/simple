# Render Performance Redesign Plan (2026-08-06)

Diagnosis (claim-verified): `doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md`.
Relationship to existing plans:

- `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (workstreams A–E)
  remains the SimpleOS screens umbrella. This plan is the deeper perf/compiler
  redesign it feeds into. Overlaps and supersessions are listed in §12.
- The unified packed-scene campaign (L0–L9, landed) is the physical scene
  basis. This plan is **additive V2 repair**, not a new scene architecture.
  No GuiIR/WebIR (standing rejected decision).

## 0. Decisive first milestone

Not Vulkan, not AVX-512. A warm frame where:

```
allocations             = 0
scene copy bytes        = 0
full readback bytes     = 0
unchanged raster pixels = 0
physical forward hops   = 0
```

Only then do SIMD/GPU operate on real packed workloads.

## 1. Target architecture

```
WM | GUI | Web  (private semantic state, stable IDs/revisions/deltas)
      ↓ compile-time layer/service views (aliases + forwarding + layer-eq
        types, ERASED before executable MIR)
UiSceneColumnArenaV2  (DrawIR-v3 columns, leases, generations, MutSpan writers)
      ↓ SceneDeltaRef
Common Render Optimizer (revisions, property trees, retained chunks, damage,
                         tiles, culling, conservative occlusion, resources,
                         glyph atlas, batching)
      ↓ PreparedRenderPlan
Placement/Cost Planner (dirty px, op mix, residency, transfer/sync, power)
      ↓                    ↓
CPU plan optimizer     GPU plan optimizer
CpuKernelTable         Common GpuRenderPlan → Vulkan | Metal | D3D12
      └───────── persistent compositor, damage-aware presentation ─────────┘
```

Key distinction: **architectural layers are compile-time boundaries;
optimization layers are plan stages; runtime wrappers are not required for
every architectural layer.** GUI/Web/WM write one packed scene; the optimizer
sees it once; the executor receives one prepared plan.

Layer responsibilities and allocation permissions:

| Layer | Responsibility | Runtime allocation |
|---|---|---|
| L0 semantic | WM windows, widget tree, DOM/CSS/layout | persistent semantic state only |
| L1 layer/service view | dependency check, aliases, forwarding, type projections | none — compiler-only |
| L2 packed scene | DrawIR columns, stable IDs, owners, revisions | session alloc; zero steady-frame alloc |
| L3 common optimization | invalidation, chunks, damage, culling, resources | frame arena / preallocated sidecars |
| L4 placement | CPU/GPU/pass selection + fallback receipts | fixed plan workspace |
| L5 CPU / GPU optimization | spans, kernel selection, tiles / instances, uploads, pass graph | per-thread scratch / persistent rings |
| L6 API backend | Vulkan/Metal/D3D12 encoding | backend-managed persistent pools |
| L7 presentation | swap, composite, partial update, scanout | frame-ring resources only |

## 2. Repair the packed memory path first (critical path F1→F2→F3)

### F1 — class/reference semantics (language contract)

The arena writer's copy workaround exists because a class instance stored as
another class's field is a **value copy under the tree-walk interpreter**
(`draw_ir_v3_native_writer.spl:14-19`, verified) while other engines differ.
Contract to enforce across interpreter, seed JIT, pure-Simple JIT/AOT,
SimpleOS:

- `struct` = value semantics; `class` = identity/reference semantics.
- Assigning a class to a field copies the reference, never the object.
- `clone()` / explicit value-copy required to duplicate.
- Borrowed exclusive access stays exclusive through aliases.
- Tests: nested fields, optionals, arrays of class refs, trait fields,
  function parameters — same corpus, same hashes, every engine.

Until F1 lands, every zero-copy scene abstraction is engine-dependent.

### F2 — packed span ABI

Safe handle, not a raw host pointer:

```
struct BufferSpanRef:
    object_slot: u32
    object_generation: u32
    byte_offset: u32
    byte_length: u32
    element_count: u32
    element_stride: u32
```

Runtime resolves once to `SimplePackedSpanV1 {base, byte_length,
element_count, element_stride, flags}` (C, per the pure-Simple-first / C-not-
Rust hardware policy). Required: no boxing, no temp rows, no gather/scatter,
stale-generation refusal, one bounds/generation check per submitted batch.
Interpreter mode uses the scalar oracle and must not claim SIMD performance.

### F3 — UiSceneColumnArenaV2

New files (frozen DrawIR-v3 schema and v1 port untouched):

- `src/lib/nogc_sync_mut/ui/ui_scene_column_arena_v2.spl`
- `src/lib/nogc_sync_mut/ui/draw_ir_v3_direct_writer_v2.spl`
- `src/lib/common/ui/ui_scene_delta_v2.spl`
- `src/lib/common/ui/ui_scene_ports_v3.spl`

Preallocated front/back columns; direct indexed MutSpan writes; stable
producer partitions + component IDs + generations; dirty byte/ID ranges; no
writer-owned temp arrays; no row-commit copy; no mid-frame compaction; growth
only at frame boundary; typed refusal on partition overflow. Incremental
frames update stable slots and emit:

```
struct SceneDeltaRef:
    scene_generation: u32
    changed_table_mask: u32
    dirty_range_start: u32
    dirty_range_count: u32
    damage_start: u32
    damage_count: u32
```

Producer IDs remain **arena-absolute** (standing lesson: producer-local IDs
pass single-producer tests and break composition).

## 3. Zero-cost layers and typed forwarding (language feature — lanes C0–C5)

### C0 — layer declarations

```
layer draw
layer gui uses draw
layer web uses gui, draw
layer wm uses gui, draw

@layer(gui)
module gui.widgets
```

Rules: acyclic; calls only same-layer or declared-downward; lower layers never
import higher semantic state; events go up via route data, not reverse
imports; layers create no runtime objects.

### C1 — layer-equivalent types (implicit-by-name, explicit-by-tag)

Same-name fields inferred; renames tagged:

```
@layer_eq(draw.DeviceRect)
struct GuiBounds:
    @layer_field(x) left: i32
    @layer_field(y) top: i32
    @layer_field(width) extent_x: i32
    @layer_field(height) extent_y: i32
```

Conversion is a compile-time proof, zero executable ops (same SSA value/
address). Proof covers: size, alignment, field types/offsets, enum
discriminants, ownership/mutability, lifetime, address space, endianness,
unit/coordinate tags, pixel format/color space/alpha, ABI version + dynSMF
fingerprint. NOT layer-equivalent (must stay explicit ops): CssLogicalRect→
DevicePixelRect, straight→premultiplied color, host→device buffer, document→
window point, UTF-8 byte↔scalar index. Type vocabulary: `@unit(css_px)`,
`@space(document)`, `@color(srgb8)`, `@alpha(premultiplied)`.

### C2 — typed forwarding instead of generated wrappers

Keep the surface syntax (`alias GuiPaint = draw`, `fn fill_rect =
draw.fill_rect`) but the parser emits a typed declaration, never a source
body:

```
HirForwardDecl { logical_symbol, receiver_projection, target_symbol,
                 layer_view_map, effect_summary, logical_join_point_id }
```

Compiler sequence: resolve layer DAG → prove layer-eq views → transitive
forwarding graph → assign join-point IDs → weave static aspects → specialize
session service table → collapse chains → erase identity views →
devirtualize single-target calls → inline/SROA → verify noalloc/nocopy/
effects → lower ONE physical call. `WebPainter.submit → GuiPainter.submit →
Draw2DService.submit → CpuRenderExecutor.execute` becomes
`CpuRenderExecutor.execute(plan, target)`.

### C3 — logical AOP join points

Aspects target logical edges (`forward(src,dst)`, `layer_view(a,b)`,
`scene_commit(kind)`, `render_batch(kind)`, `event_route(owner)`,
`fallback(class)`, frame boundary) — a business-logic-free forwarder need not
exist physically for advice to observe it. Three modes: static weave (zero
disabled overhead), startup dynload (immutable AspectPlan before session,
tables specialized once), live reload (plan swap at frame boundary,
epoch/RCU retirement). Never per-pixel/glyph/span/tile join points; hot-path
join points only at frame/commit/plan/batch/submit/event-batch/fallback.
Aspect state in a sidecar keyed by slot+generation; advice declares
`@readonly @noalloc @bounded_time`.

### C4 — effect verifier

`@noalloc`, `@copy_budget(0)`, `@bounded_loop` verified on **post-weave,
post-collapse MIR**: rejects allocator calls, container growth, hidden
boxing, prohibited copies.

### C5 — mechanical gates (`@zero_forward_path`)

Compiler reports per hot entrypoint: `logical_forward_edges=N,
physical_forward_calls=0, layer_view_copy_bytes=0, temporary_allocations=0,
dynamic_dispatches<=1/batch`. Compilation FAILS when a claimed identity view
changes size/alignment/ownership/address-space, needs unit/color conversion,
allocates, copies, or calls a user conversion.

## 4. Common optimizer (lanes O0–O4)

Backend-ignorant `prepare(scene, delta, viewport, capabilities, scratch) ->
PreparedRenderPlanRef`. Ordered passes:

1. **Revisions/invalidation** — separate `semantic/style/layout/paint/
   transform/clip/resource/event` revisions; mutations mark minimal sets.
2. **Property trees** — transform/clip/effect/scroll/surface; window move =
   one transform-node update.
3. **Retained paint chunks** — grouped by owner/transform/clip/effect/
   surface/resources/order; cache key = component_generation +
   paint/property/theme/scale/viewport/capability generations.
4. **Damage** — exact rects for small changes AND dirty tile sets; separate
   scales (coarse grid ~128–256 px, CPU tiles ~32–64 px, GPU bins ~128–256
   px), profile-measured, not hard-coded.
5. **Visibility + conservative occlusion** — cull hidden/zero-area/off-
   viewport/covered-by-provably-opaque; any uncertain alpha/filter/blend/
   rounding/transform disables that occlusion decision; exact paint order
   preserved.
6. **Resource interning/atlases** — content hash + semantic metadata for
   images, gradients, paths, shaped runs, glyph masks, clip masks, pipelines.
7. **Batching/fusion** — only when target, order, blend, clip/effect, format,
   resources, opacity all match; never reorder overlapping translucency.
8. **Pass graph** — backend-neutral `RenderPassNode` DAG + transient
   lifetimes; GPU maps to passes, CPU executes same graph on tiles.
9. **Placement** — per pass/batch on dirty px, op type, residency, transfer/
   sync cost, queue load, latency, power, correctness evidence. Never GPU
   just because one exists; never widest SIMD just because the bit is set.

**Optimization registry**: each optimization = descriptor {stage,
preconditions, capabilities, exactness class, cost model, verifier,
fallback}. Promoted only after: preconditions proven, scalar parity, shadow
execution divergence-free, wins its bucket, p95/memory inside gate, fallback
receipt-backed. (The current SIMD regression — diagnosis claim 1/5 — is the
proof that capability presence is not a promotion criterion.)

## 5. CPU scalar + SIMD (lanes P0–P5)

- **One kernel contract, many providers** (`CpuIsaProvider`: probe,
  register_kernels, self_test vs scalar oracle, calibrate). Registry key =
  operation × pixel format × alpha × alignment × contiguity × size bucket ×
  mask × filter. Session builds one `CpuKernelTable` once.
- Size buckets: 0–15 scalar; 16–63 scalar/narrow; 64–255 SIMD; 256+ SIMD
  possibly threaded; large overwrite = measured streaming-store variant.
- Providers: x86 (scalar/SSE2/SSSE3-SSE4.1/AVX2/AVX-512BW-VL — separate
  variants, fixes today's `Avx512→"avx2"` aliasing), AArch64 (Neon, SVE/SVE2
  VLA), Arm32 (optional Neon), M-profile (optional MVE), RISC-V (RVV 1.0
  strip-mined, Zve profiles); future providers register, never extend a core
  enum.
- Kernel set v1: fill_const, copy_span/rect, scroll_rect, src_over_const/
  image, mask_src_over, glyph_mask_blend, nearest/bilinear_blit, linear/
  radial_gradient, format_convert, (un)premultiply, blur_h/v,
  coverage_combine. Kernels receive packed spans or `SimpleSpanOpV1` batches
  — **one batch FFI call**, never boxed arrays or per-row calls.
- **Correctness**: scalar is the executable oracle; one exact /255 rounding
  formula; every provider passes exhaustive alpha/boundary, randomized,
  misaligned, tails, overlap, zero-length, cross-page, target-endian tests;
  register only bit-exact kernels.
- **Performance**: candidate must beat selected scalar by ≥10% in its bucket
  with acceptable p95, else the table keeps scalar; calibration cached by CPU
  model + ABI version + kernel hash + power profile; deterministic mode uses
  a certified table.
- **Threading**: one persistent pool/session; exclusive output tiles/bands;
  no shared cache lines; paint order within tile; scalar below measured
  dirty-area threshold; separable filters; scroll = copy + exposed damage.

## 6. GPU plan + backends (lanes G0–G4)

- **G0 common plan** `GpuRenderPlan {passes, batches, uploads, transients,
  capability_key}`; common optimizer does instances, batching, indirect args,
  dirty-range uploads, dependencies, transient lifetimes, residency.
  Backends only encode.
- Persistent session per backend: device/queue, swapchain, allocators, 2–3
  frame contexts, upload rings, pipeline cache, descriptor/argument
  allocator, atlases, transient heap, sync objects. Warm frames never:
  recreate device/pipelines, allocate a full framebuffer, device-idle, read
  back, or submit per-widget.
- **G1 Vulkan**: early persisted pipelines + VkPipelineCache per device
  identity; frame command pools + staging rings; dirty tiles into ≤2 command
  buffers; fences/timelines not wait-idle; exact barriers from the pass
  graph; dirty-range uploads only. (Host caveat on record: this dev host's
  QEMU cannot instantiate virtio-gpu-gl / Venus — E2/E3 stay parked; see
  `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`.)
- **G2 Metal**: persistent PSOs + argument buffers, triple buffering, ~1
  command buffer/frame, heaps for proven-disjoint transients, GPU-resident
  textures, no CPU mirror of GPU-only surfaces.
- **G3 D3D12**: immutable PSO cache, persistent shader-visible descriptor
  heaps (suballocate; heap switches bounded), per-frame allocators + upload
  rings, batched precise barriers, pipeline-library persistence.
- **G4 route modes**: keep the existing `cpu_selected` vs `gpu_fallback`
  receipt contract (`draw_ir_v3_execution_route.spl`) and add CPU
  subconfiguration under it:

```
render:
  mode: cpu_reference          # cpu_reference | hybrid_vector_gpu | resident_gpu
  cpu:  {vector: auto, threads: auto, calibration: cached, deterministic: false}
  gpu:  {backend: auto, frames_in_flight: 3}
  verification: {shadow_frames: 30, exact_integer_pixels: true}
```

Forced ISA/backend fails closed if unavailable; `auto` states its reason in
the receipt.

## 7. WM / GUI / Web / events adoption (lanes U0–U3)

- **WM**: window = stable ID+generation, property-tree nodes, retained chunk
  range, optional cached backing surface, damage region, event-owner record.
  Move = update transform + damage old/new + recompose cache + repaint only
  exposed. Replace production PPM/file transport with slot-backed shared
  surfaces / shm ring / direct compositor references; PPM = test/export only.
- **GUI**: depends on `Draw2DSceneService` (begin_update → DirectSceneWriterV2
  → commit_update → SceneDeltaRef), not Engine2D concretes. Widgets update
  retained component ranges; GUI-hosted Web gets a sublease in the same arena.
- **Web style**: `PropertyId: u16` enum (append-only, generated),
  `Declaration {property, value_id, flags}`, `ComputedStyleHot` (display,
  position, visibility, opacity, color/background IDs, width/height value
  IDs, layout/paint flags) + cold side table. `apply_declarations` iterates
  only existing declarations — O(k). Parse names→PropertyId once, values→
  typed once; intern immutable computed styles; selector indexes +
  invalidation sets; containment where semantics allow; CSS logical units
  stay distinct from device-pixel layer-eq types; DrawIR deltas only for
  affected components; shaped-run + glyph caches.
- **Events**: keep the preallocated ring; make the whole path allocation-free.
  One POD `InputPacket`; Host/Wm/Gui/Web views only where representation and
  units are identical (host→web coordinate transform is an explicit property-
  tree op, not a view). Routing: ring → batch → one hit test on the DrawIR
  hit-shape index → `RouteToken {scene_generation, owner_id,
  owner_generation, path}` → owner chain → handler. `drain_into(batch)` not
  allocating `drain()`; SPSC power-of-two rings, release/acquire; coalesce
  move/wheel, never down/up/key/text/focus/close; reject stale generations;
  AOP only at batch boundaries.

## 8. Allocation and capacity model

Four classes: session-persistent (arena, atlases, pipelines, pool), frame
arena (plan nodes, dirty ranges), per-thread scratch (coverage, filter rows),
GPU ring/heap (fence-delimited). Steady-state invariants:

```
heap_allocations_per_warm_frame   = 0
scene_copy_bytes                  = 0
full_frame_readback_bytes         = 0
pipeline_creations_per_warm_frame = 0
descriptor_heap_switches          = bounded
event_allocations                 = 0
```

Capacity: high-water marks + EWMA + retained p99 per table; configured
headroom; refuse or schedule rebase on overflow; grow only at safe frame
boundary; never mid-emission; fixed-capacity low-memory mode for SimpleOS.
Enforced by C4's `@noalloc @copy_budget(0) @bounded_loop` MIR verifier.

## 9. Parallel-agent waves

Discipline carried over from the screens plan: exclusive path ownership,
count-based verdicts, deliberate sabotage tests, one integration owner for
shared registry/switch files.

```
C0 → C1 → C2 → C3 → C4          (compiler lane; C5 integration owner)
F0 ─────────────────────────┐
F1 → F2 → F3 ───────────────┼→ O0..O4 → placement
W0 ─────────────────────────┘        ↓
                        CPU lanes (P0..P5)   GPU lanes (G0..G4)
                                 └────────┬────────┘
                            WM/GUI/Web adoption (U0..U3, U4 cutover)
                                          ↓
                            parity/perf promotion (V0, V1)
```

Wave 0 (foundation): F0 perf-receipt v2 + engine-identity fail-closed gate;
F1 class identity; F2 span ABI; F3 arena V2; F4 presentation audit (no normal
readback); W0 web O(k) declarations. **F1→F2→F3 is the performance critical
path.** Wave 1: C0–C5. Wave 2: O0 revisions, O1 property trees/chunks, O2
damage/tiles/occlusion (sabotage: mark translucent opaque → gate must go
red), O3 resources/text, O4 placement/registry. Wave 3A CPU: P0 scalar
oracle+registry, P1 x86, P2 Arm, P3 RISC-V, P4 scheduler/filters, P5 sole
provider-aggregation owner. Wave 3B GPU: G0 plan (CPU mock encoder proves
deterministic command plan), G1–G3 concurrent after G0 freezes, G4 selection.
Wave 4: U0 GUI, U1 Web deltas, U2 WM cached surfaces + transform-only move,
U3 events, U4 flag-guarded cutover at one dispatch site, V0 differential/
property suites (no vacuous all-zero pass; sabotage required), V1 promotion.

## 10. Test matrix and gates

Workloads: 320×240 / 1080p / 4K / 8K × damage {0, 0.1, 1, 10, 100}% × scenes
(solid, mixed widgets, text-heavy, scrolling, window move, image scale,
translucent overlays, rounded clips, gradients, blur/shadow, Web-in-GUI-in-WM,
event storm) × identities (interpreter/seed = correctness only; pure-Simple
AOT, x86/AArch64/RISC-V native, Vulkan/Metal/D3D12, SimpleOS/QEMU, target SBC
= performance).

Frame receipt metrics: stage times (style/layout/delta/opt/plan/raster/
present) + semantic_nodes_touched, style_properties_applied,
draw_rows_written, scene_copy_bytes, dirty/rasterized_pixels, culled/
occluded_ops, kernel_calls, ffi_calls, allocations, upload/readback_bytes,
gpu_submits, pipeline_creations, descriptor_heap_switches, glyph/tile cache
hits, forwarding_physical_hops, layer_view_copy_bytes, event_allocations.

Blocking correctness: scalar authoritative; ISA variants byte-identical; GPU
integer primitives byte-identical where representable; per-op (not global)
filter tolerances; old/new shadow parity; nonzero-pixel proof (two empty
buffers cannot pass); stale generations fail closed; unmet preconditions
disable the optimization, never approximate.

Blocking structural (warm): the §8 invariants, plus GPU submits ≤2/frame,
dispatch ≤1/prepared batch, style work O(declarations), idle raster pixels =
0, idle scene rows rewritten = 0.

Promotion: ≥10% p50 win in bucket, p95/RSS inside budget, genuine execution
proven by counters, no hidden fallback. Expectations: Simple AOT scalar
approaches C scalar (vs today's 31x, diagnosis claim 2); SIMD beats scalar
for large spans or stays unselected; 1% dirty ⇒ ≤5% full-frame raster bytes;
transform-only move ⇒ zero repaint; repeated text ⇒ zero shaping/raster/
upload; 8K80 claims only per declared damage class on specified hardware.

Sabotage tests (each lane breaks one invariant, proves its gate reds):
value-copy class assignment; allocating MutSpan; restored writer-local
arrays; css-px-as-device-px layer_eq; surviving forwarding wrapper in MIR;
allocation under @noalloc advice; translucent-marked-opaque occlusion;
AVX2 rounding change; vkDeviceWaitIdle; stale event-owner accepted; restored
wide property probing. A gate green under sabotage has proven nothing.

## 11. Execution order

1. F0 receipts + engine-identity gates. 2. F1 class semantics. 3. F2 span
ABI. 4. F3 direct writers. 5. F4 kill normal-frame readback/PPM. 6. O0–O2
revisions/damage/chunks. 7. W0 O(k) styles. 8. P0 scalar batch oracle.
9. P1–P3 ISA providers behind per-op dispatch. 10. G0 then G1–G3.
C-lanes proceed concurrently with 2–7 (existing aliases can be represented
as typed forwarding nodes internally before the new syntax lands).

Explicitly avoided: new GuiIR/WebIR; runtime wrapper per layer; per-widget/
glyph/tile GPU submits; per-row FFI with gather/scatter; full readback for
presentation; one global widest-SIMD decision; implicit coordinate/unit/
color/alpha/host-device conversions; optional aspect fields in core objects;
per-pixel dynamic AOP; perf claims from interpreter/seed; enabling an
optimization because a capability bit exists.

## 12. Reconciliation with screens workstreams (A–E)

| Screens item | Status vs this plan |
|---|---|
| WS-D damage tracking (`backend_software.spl`, zero consumers) | **Superseded in mechanism** by O2/§4-pass-4; the D3 investigation's finding (per-op `present()` clears damage; `get_pixel_buffer()` is a live alias) is a *precondition defect* F4 must fix before any consumer is wired. See `ws_d3_damage_present_investigation.md` §9. |
| WS-D SIMD env knob (`SIMPLE_2D_SIMD=auto|off|…`) | **Superseded** by P0–P5 per-operation kernel table; the knob survives as the `render.cpu.vector` config surface only. |
| WS-D occlusion culling (landed, 21/21 + 10/10) | Feeds O2; keep as the compositor-level conservative baseline. |
| WS-B ScreenHost/showcase, WS-C input HAL | Unchanged; U3 builds on WS-C's ring + `HostInputEvent` (already POD-shaped). |
| WS-E Vulkan | Unchanged and still blocked on this host (Venus gap bug); G1 defines the target contract it will adopt. |
| WS-A config/evidence | Unchanged; F0's receipt v2 extends (not replaces) the multiconfig evidence rows. |
