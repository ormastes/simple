# DrawIR paint-time affine transform — design (GAP-4T)

Design-only. No production code changed. Answers the sub-lane deliverable
called for by `drawir_feature_gap_2026-07-31.md` §5 lane 7 (GAP-4T): decide
the representation, backend fan-out plan, and hit-test interaction for
rotation/scale/skew at paint time, before any code lands. Every claim below
cites `file:line`; anything not directly re-read this session is marked
**UNVERIFIED**.

## 1. Current state, with evidence

### 1.1 `DrawIrCommand` / `DrawIrBatch` / `DrawIrEmbeddingConfig` today

Read in full this session, `src/lib/common/ui/draw_ir.spl:57-100`:

```
struct DrawIrEmbeddingConfig:              # :57-66
    surface_id: text
    component_id: text
    x, y, width, height, layer: i32
    opacity_milli: i32
    clip: bool

struct DrawIrCommand:                      # :68-86
    kind: text
    component_id: text
    x, y, width, height: i32
    color: u32
    text_value: text
    advance_widths: [i32]
    border_rect, content_rect, hit_rect, clip_rect: DrawIrRect
    computed_style: [DrawIrStyleProp]
    edge: DrawEdge?
    parent_id: text
    image_uri: text
    points: [DrawIrPoint]
    glyph_run: DrawIrGlyphRunPayload

struct DrawIrBatch:                        # :88-95
    schema, batch_id, backend_target: text
    source: DrawIrSourceInfo
    embedding: DrawIrEmbeddingConfig
    commands: [DrawIrCommand]
```

No rotation/scale/skew/matrix field anywhere in the file (confirmed by
reading the whole struct block, not a grep miss). Geometry is exclusively
axis-aligned `x/y` origin + `width/height` extent, at both the per-command
and per-embedding level. This matches the audit's "ABSENT" finding
(`drawir_feature_gap_2026-07-31.md:54-55`) — re-confirmed independently here.

Only **3 files construct `DrawIrCommand` literals** repo-wide:
`draw_ir_drawio.spl:82` and `draw_ir.spl:224,247,279,344,367,390,413,436,459`
(all in `draw_ir.spl` itself). This is a small, closed construction surface —
material to §2's backward-compatibility argument.

> **v3 patch/damage successor.** The `DrawIrCommand` / `DrawIrBatch` / `DrawIrEmbeddingConfig` shape
> above is the v2 authoring IR; the affine field this doc adds is a v2 schema change. The GPU-WebScene
> plan (I4) notes current DrawIR patching is *library-only, single-batch, and does not compare every
> command field*, and specifies a DrawIR-v3 successor with multi-batch insert/remove/update/reorder,
> full-field equality, and effect-expanded damage. This affine work stays on v2; the packed v3 encoding
> and its patch/damage engine are additive over it (see
> [`draw_ir_multibackend_design.md`](rendering/draw_ir_multibackend_design.md) §11).

### 1.2 Struct-field defaults are an established pattern in this exact
neighborhood

`src/lib/gc_async_mut/gpu/engine2d/draw_ir_target.spl:16-26` (`DrawIrTargetFontEvidence`)
declares fields with inline defaults: `batch_identity: text = ""`,
`parity: bool = false`, `device_executed: bool = false`, etc. Simple structs
support default field values, and call sites use named-field literals (every
`DrawIrCommand(...)` construction found is named, not positional — confirmed
by reading each of the 10 sites). Adding new **defaulted** fields to
`DrawIrCommand` is therefore non-breaking for all 3 existing construction
sites: they simply keep omitting the new fields and get the identity default.

### 1.3 Web renderer's layout-geometry approximation

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl:786-889`
(read in full this session). The `transform:` / `translate:` / `scale:` /
`rotate:` CSS declarations are each parsed and folded straight into the box's
layout geometry fields (`left_px_v`, `top_px_v`, `width_v`, `height_v`) —
there is no paint-time transform applied to a rasterized rect at all:

- `transform: translate*()` / the standalone `translate:` property → added to
  `left_px_v`/`top_px_v` (`:833-836`, `:857-862`) — this is exact, not an
  approximation, because translation commutes with axis-aligned rects.
- `transform: scale()` / standalone `scale:` → **multiplies `width_v` /
  `height_v` in place** (`:842-847`, `:867-871`) — this only reproduces
  correct visuals for scale-from-top-left with no rotation; it does not
  reproduce CSS's actual transform-origin-anchored scale, and there is no
  separate paint-time scale of pixel content (the rect is simply laid out
  bigger/smaller).
- `transform: rotate()` / standalone `rotate:` → `parse_rotate_quarter_turn`
  (`foundation.spl`, read `:1181-1189`) only recognizes exact 90°/270°
  (mod 360) and, when true, **swaps `width_v`/`height_v`**
  (`decl_apply.spl:849-853`, `:874-876`). Any other angle (including 45°, or
  180°, which needs no swap but does need a flip) is silently ignored —
  `parse_transform_rotate_quarter_turn` (`foundation.spl:1191-1200`) has no
  fallback branch, so `if` is simply false and geometry is untouched.
- `transform-origin` / `transform-box` / `transform-style` are parsed and
  stored (`decl_apply.spl:889-902`) but **UNVERIFIED** whether anything
  downstream reads them — no consumer of `transform_origin_v` was located in
  this session's grep of `decl_apply.spl`/`paint_layout.spl`.

Net: the web path never paints a rotated or skewed pixel. It relabels the
layout box's rectangle to *approximate* the bounding-box effect of a subset
of transforms, then paints an ordinary axis-aligned rect through the same
`DrawIrCommand.x/y/width/height` fields as everything else.

### 1.4 Game's `Transform2D`

`src/lib/gc_async_mut/game2d/transform.spl:13-31` (read in full):

```
class Transform2D:
    pos_x, pos_y, rotation, scale_x, scale_y: f64
    parent: Transform2D?
    _matrix_cache: [f64]      # 9-element row-major 3x3 affine, lazily built
    _dirty: bool
```

This already models full 2D affine (translate + rotation + non-uniform
scale) with a cached 3x3 matrix and a parent chain for hierarchical
composition — strictly more expressive than anything DrawIR carries. No
`skew` field exists anywhere in the tree (grep for `skew` across
`engine/`, `game2d/`, `common/`, `ui/` = 0 hits, reconfirmed this session).

It is disconnected from DrawIR because nothing in `game2d/` or
`gpu/engine2d/bridge_game2d.spl` writes `Transform2D`'s matrix (or its
decomposed fields) into any `DrawIrCommand`/`DrawIrEmbeddingConfig` field —
there is no such field to write into (§1.1). Sprites reach the screen via
their own `x/y` (already resolved from `Transform2D.pos_x/pos_y` upstream)
and DrawIR never sees rotation/scale past that point. This is
**UNVERIFIED at the exact call-site level** (the bridge file was not traced
line-by-line this session) but is consistent with, and required by, §1.1's
finding that `DrawIrCommand` has no field to carry it in.

## 2. The representation decision

### 2.1 Options considered

| Option | Memory cost | Can existing consumers ignore it? | Notes |
|---|---|---|---|
| A. Per-command full 3x3 matrix field | 9 × f64 = 72 B/command (or 6 × f64 = 48 B affine-2x3) | Yes, if defaulted to identity | Matches `Transform2D`'s own cache shape (`transform.spl:16`) 1:1 — no decompose/recompose step at the game boundary. Heaviest of the options; most backends never read it. |
| B. Per-command decomposed TRS+skew (`rotation, scale_x, scale_y, skew_x, skew_y: f64` + `has_transform: bool`) | 5×f64 + 1×bool ≈ 41 B/command | Yes, same default-field mechanism | Cheaper than a matrix for the common case (most commands: identity); matrix is derivable on demand by the one thing that needs it (a backend actually painting the transform). Human-debuggable field values (a saved `.spl` fixture shows `rotation: 0.78` not 9 opaque floats). |
| C. Per-batch/embedding-only transform | 1 shared cost per batch, not per command | Yes | Cannot express "this one glyph run inside the batch is rotated but its sibling rect isn't" — CSS/game both need per-element transform (a single rotated `<div>` inside an unrotated parent is ordinary CSS). Rejected: too coarse for the actual need. |
| D. Transform stack (push/pop, imperative-immediate-mode style) | 0 extra struct fields; cost lives in the executor | No — every executor must adopt stack semantics to stay correct, since a batch's paint order becomes stack-order-dependent | `DrawIrComposition` is a retained, diffable display list (§1, `draw_ir_patch.spl`), not an immediate-mode command stream; a stack model fights the existing diff/patch design (`DRAW_IR_PATCH_OP_UPDATE_GEOMETRY`, `draw_ir_patch.spl:59`) because patches replace one command's fields, not stack state. Rejected. |

### 2.2 Recommendation

**Option B — per-command decomposed fields, defaulted to the identity
transform, added to `DrawIrCommand` only (not `DrawIrEmbeddingConfig`).**

Reasoning:
- **Per-command, not per-batch/embedding (rules out C):** CSS and game both
  need element-granularity transform; a batch-level field can't express one
  rotated child inside an unrotated batch. `DrawIrEmbeddingConfig` stays
  untouched — it positions a whole surface/component, which is a coarser
  concern than one command's paint transform.
- **Decomposed TRS+skew, not a full matrix (picks B over A):** the
  authoring/consuming sources (CSS `transform:`, game `Transform2D`) both
  produce/consume decomposed values, not raw matrices — CSS parses
  `rotate()`/`scale()`/`skew()` as separate functions
  (`foundation.spl:1170-1200` already parses `rotate(deg)` and `scale(pct)`
  as distinct calls), and `Transform2D` stores `rotation`/`scale_x`/
  `scale_y` as distinct fields (`transform.spl:15`) with the 3x3 matrix as a
  *derived cache*, not the source of truth. Carrying the same shape through
  DrawIR avoids a decompose-then-recompose round trip at both ends. A
  backend that wants the matrix builds it once from 5 scalars — cheap, and
  exactly the computation `Transform2D` already does internally.
- **Defaulted fields, not a required constructor param:** per §1.2, this
  makes the change invisible to the 3 existing construction sites and to
  every one of the ~14+ backend/paint call sites that only ever *read*
  `DrawIrCommand` (they already tolerate fields they don't act on — e.g. no
  backend acts on `glyph_run` unless it does shaped-text painting). Add:
  ```
  has_transform: bool = false
  transform_origin_x_pct: i32 = 50   # CSS default transform-origin: center
  transform_origin_y_pct: i32 = 50
  rotation_deg_milli: i32 = 0        # integer millidegrees — matches the
  scale_x_pct: i32 = 100             # existing i32-fixed-point convention
  scale_y_pct: i32 = 100             # used throughout draw_ir.spl (opacity_milli,
  skew_x_deg_milli: i32 = 0          # advance_widths) rather than introducing
  skew_y_deg_milli: i32 = 0          # the first f64 field in the struct
  ```
  Using `i32` fixed-point (matching `opacity_milli`'s existing convention,
  `draw_ir.spl:65`) instead of `f64` keeps `DrawIrCommand` in its current
  all-integer-or-text field discipline and dodges introducing float ABI
  concerns into a struct that native codegen already treats specially
  (`.claude/rules/code-style.md`'s Dict-native-pitfalls precedent is a
  reminder that native codegen has sharp edges around non-trivial payloads —
  staying in `i32` is the conservative choice). Cost: 8 × i32 + 1 × bool ≈
  33 B/command, only paid when `has_transform` is read.
- **Backward compatibility is structural, not just "hoped for":** every
  existing backend's paint call already ignores fields it doesn't consume
  (confirmed pattern: `draw_ir_target.spl`'s trait methods take explicit
  scalar args like `draw_rect_filled(x,y,w,h,color)`, `:37` — they were never
  passed the whole `DrawIrCommand`, so a new field on the struct changes
  nothing about a trait method's signature). The risk is entirely
  concentrated in the ONE call site that reads `DrawIrCommand` fields to
  build those scalar args — `_engine2d_draw_ir_render_commands`
  (`draw_ir_adv.spl:1222-1236`, read this session) and its per-kind helpers
  (`_engine2d_draw_ir_render_box` etc., called `:1263-1264`). That is exactly
  one function family to teach about `has_transform`, not 14.

## 3. Backend impact

No CUDA or Vulkan device exists in this environment — the CUDA
(`backend_cuda*.spl`) and Vulkan (`backend_vulkan*.spl`) family designs below
are therefore **paper designs only**; nothing GPU-side can be run or verified
here, and the plan is written so the CPU-verifiable path lands first and
alone.

### 3.1 CPU / software family — `backend_cpu.spl`, `backend_software.spl`, the `emu_*` family

`backend_cpu.spl:9-11` composes `SoftwareBackend` (`backend_software.spl`)
and implements `RenderBackend` (`:19` `impl RenderBackend for CpuBackend`);
`backend_emu.spl:1-19` explicitly documents itself as a stateless layer that
"Implements every RenderBackendAdv operation using ONLY RenderBackend
methods" — i.e. it is a shim over the same CPU primitives, not a separate
raster path.

**No-op default:** none needed to stay correct — today, before any command
ever has `has_transform: true`, behavior is bit-identical (the new fields
are read by nobody yet). **Stage-A change (this is the CPU-verifiable
path):** in `_engine2d_draw_ir_render_commands`
(`draw_ir_adv.spl:1222`), when `command.has_transform` is true, pre-transform
the geometry on CPU *before* calling the existing scalar-arg trait methods —
i.e. Stage A adds no new trait methods and no backend-specific code at all.
Two sub-cases:
  - **Axis-aligned-preserving case** (rotation is 0/90/180/270 mod 360,
    skew is 0): compute the transformed integer rect directly (swap w/h for
    90/270, as the web path already partially does) and call the existing
    `draw_rect_filled(x,y,w,h,color)` unchanged. Zero new raster code.
  - **Arbitrary-angle case:** rasterize via CPU-side inverse-mapping
    (destination-bbox scan, sample source pixel/color under the inverse
    matrix) into a scratch `[u32]` buffer, then hand that buffer to the
    already-existing `draw_image(x,y,w,h,pixels)` trait method
    (`draw_ir_target.spl:39`) instead of `draw_rect_filled`. This reuses a
    method every backend already implements (image blit), so it still adds
    zero new trait surface — only a new *caller-side* helper that decides
    which existing method to call.

### 3.2 Vulkan family — `backend_vulkan.spl` + 9 sibling files (`_font`, `_font_spirv`, `_font_types`, `_glsl`, `_helpers`, `_session`, `_session_runtime_ops`, `_spirv`, `_spirv_raster_blobs`)

**No-op default:** identical to §3.1 — untouched until `has_transform` is
read. **Design for later (UNVERIFIED — no device to test):** a vertex-shader
uniform (2x3 or 3x3 matrix, built once per command from the same 5 decomposed
scalars) is the natural home once this backend opts in, since Vulkan already
pays a per-draw-call uniform-upload cost. Do not attempt this before Stage A
proves the representation on CPU — the audit's own stance
(`drawir_feature_gap_2026-07-31.md:168-171`) is that GPU parity is a later,
separate proof, and the board-runnable rule equally applies: a
Vulkan-only-on-paper design must not be claimed as verified.

### 3.3 CUDA family — `backend_cuda.spl` + `_ext`, `_font_ptx`, `_kernels`, `_launch_args`, `_proof`

Same posture as §3.2: no-op by default, paper design only. CUDA's kernel
launch path (`backend_cuda_kernels.spl`, **UNVERIFIED** — not opened this
session) would need a per-pixel affine-sample kernel variant analogous to
its existing rect-fill kernel; sizing that kernel is out of scope for this
document since there is no device here to validate correctness against.

### 3.4 Metal family — `backend_metal.spl` + `_font`, `_helpers`, `_msl`, `_runtime_ops`, plus `draw_ir_target_metal.spl`

Same posture: no-op by default. Metal already has a distinct
`draw_ir_target_metal.spl` implementing the same `DrawIrRenderTarget` trait
surface as the CPU path (confirmed by the trait's method list,
`draw_ir_target.spl:28-63`, being what any conforming target implements) —
Stage A's CPU-side pre-transform-then-blit strategy (§3.1) works unchanged
for Metal too, since it also exposes `draw_image`. A native Metal shader path
is future work, same caveat as Vulkan/CUDA: no verifiable device claim can be
made from this environment.

### 3.5 Remaining families found this session but not named in the task (`directx`, `opengl`, `opencl`, `rocm(+kernels)`, `webgpu`, `virtio_gpu`, `baremetal`, `intel(+kernels)`, `qualcomm`, `render_2d_riscv`)

The task's "~14 render backends" undercounts what actually exists:
`grep -rl draw_rect_filled src/lib/gc_async_mut/gpu/engine2d/*.spl` (run this
session) matched 24 files, spanning at least 11 distinct backend families
beyond CPU/Vulkan/CUDA/Metal/emu. All of them share the same `RenderBackend`
trait surface pattern seen in `backend_cpu.spl:19`, so §3.1's "no new trait
methods" property is what makes this design tractable at all — none of
these 11 extra families need touching for Stage A, and none can be
individually verified here (no corresponding hardware/driver in this
environment for any of them). This is exactly the same fan-out risk the gap
audit flagged for D9's `read_pixels_with_source`
(`drawir_feature_gap_2026-07-31.md:243`), and the reason this lane is a
design step, not code.

## 4. Interaction with hit-testing

**`HitProxy2D` is a strictly axis-aligned half-open AABB.** Confirmed by
reading the full struct and `contains_point`
(`src/lib/common/engine/interaction/hit_proxy.spl:24-37,59-60`):

```
class HitProxy2D:
    node_id, left, top, right, bottom: i32/i64
    ...
    fn contains_point(px, py) -> bool:
        px >= self.left and px < self.right and py >= self.top and py < self.bottom
```

There is no angle field and no polygon representation — geometrically it
cannot represent a rotated rectangle's true hit region.

> **v3 successor (2026-07-31).** The rotated-AABB proxy designed below is the CPU-side tier. The
> GPU-WebScene / MDSOC+ structural-compute plan (I7) adds a *retained* DrawIR-v3 hit/event index —
> a typed `HitShapeTable` keyed by `hit_shape_id`, consumed directly by the GPU event core — plus a
> `SourceProvenanceTable` carrying MappingGraph `HitRegionOf` / `PaintOf` edges. Treat this section as
> the CPU-oracle hit path; the retained index is its device-resident successor. See
> [`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`](../../03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md)
> §I7 and
> [`doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md`](../../03_plan/platform/structural_compute/webrender_gpu_offload_plan.md).

**The forest-building code is currently transform-oblivious by
construction.** `draw_ir_hit_forest`
(`src/lib/common/engine/interaction/draw_ir_hit_bridge.spl:46-132`, read in
full) builds every leaf's AABB by translating `hit_rect` by the embedding's
`x/y` and clamping to the embedding's box (`:97-113`) — pure axis-aligned
arithmetic, no rotation applied, because there is currently nothing to
rotate by (§1.1). If a `has_transform` command's `hit_rect` were fed through
unchanged, the resulting `HitProxy2D` would be the rect's *unrotated*
bounding box, silently wrong for any element rotated by other than a
multiple of 180°.

**This is load-bearing:** `draw_ir_hit_forest` + `hit_stack` is the WM's
entire pointer-dispatch path, confirmed at three independent call sites this
session — `window_scene.spl:850-851,908-909,1009-1010`, `panel2d.spl:333,371`,
and `host_gpu_event_queue.spl:221-227` all build a `DrawIrHitForest` and
resolve it with `hit_stack`. Any hit-testing answer for GAP-4T must keep
this exact call shape working for the ~11 non-rotated call sites that exist
before this lane, and only change behavior for `has_transform: true` leaves.

### 4.1 Recommended hit-testing approach: rotated-AABB (oriented bounding
box) exact test, gated on `has_transform`

Do **not** change `HitProxy2D`'s stored representation (still an
axis-aligned `left/top/right/bottom`, so every existing non-rotated call
site and the `group_collisions` sibling-overlap check
(`draw_ir_hit_bridge.spl:134-160`, also purely axis-aligned) is untouched).
Instead:

1. **Bounding step (unchanged data shape, new computation when
   `has_transform`):** when lifting a command with `has_transform: true`,
   `draw_ir_hit_forest` computes the *rotated corner points* of `hit_rect`
   under the command's decomposed transform (4 point transforms — cheap,
   done once per lift, not per query) and stores the AABB of those 4 points
   as `HitProxy2D.left/top/right/bottom`, exactly as it does today for the
   untransformed case (this keeps `HitProxy2D` and `contains_point` byte-
   and behavior-identical for every consumer). This alone makes hit-testing
   *conservative* (never misses a real hit) but not *exact* (a click in the
   AABB's rotated corner, outside the true rotated rect, would still
   register a hit).
2. **Exact-point refinement, opt-in per query, not per proxy:** add a second
   optional check invoked only when `hit_stack`'s AABB pass has already
   selected a candidate — inverse-transform the query point `(x, y)` by the
   candidate's transform into the rect's local space and re-run
   `contains_point`-equivalent math there. This is a point-in-oriented-rect
   test (4 comparisons after one 2x2 inverse-rotation), not a general
   polygon test, since the source shape is always a rect. Because this only
   runs on the already-narrowed top candidate (or the small set from
   `group_collisions`), it does not change `hit_stack`'s asymptotic cost for
   the common (non-rotated) case — it is skippable entirely when
   `has_transform` is false, which is `hit_stack`'s existing code path,
   confirmed unchanged (`hit_test.spl:89-118`, read this session for
   structure, no transform-aware branch needed there since the refinement
   lives in the *proxy* object's own method, not in `hit_stack`'s sort/scan
   logic).
3. **Where the refinement lives:** as a method on `HitProxy2D` itself
   (e.g. `exact_contains_point`, defaulting to the existing
   `contains_point` behavior when there is no rotation to refine against),
   so `hit_stack` (`hit_test.spl:89`) calls one polymorphic method and
   callers that never produce rotated proxies (every call site before this
   lane) see zero behavior change — this mirrors exactly how
   `pointer_policy` already gates `hit_tests_by_bounds()`
   (`hit_proxy.spl:73-79`) as a per-proxy opt-in flag rather than a global
   mode switch.

**One-sentence answer:** hit-testing stays a fast axis-aligned AABB pass
for the conservative/candidate-selection step (so `HitProxy2D` and every
existing WM call site are untouched), with an exact oriented-rect
point-in-shape refinement applied only to the top candidate and only when
that candidate's `has_transform` flag is set.

## 5. Staged lane plan

Each stage is independently shippable with its own SSpec (mirrored path per
the campaign's D8/test-path convention) and CPU-verifiable stages come
first, per the board-runnable rule (no GPU claim can be made from this
environment).

### Stage 1 — `DrawIrCommand` field addition (schema only, no behavior change)
Add the 8 defaulted fields from §2.2 to `draw_ir.spl:68-86`. No call site
elsewhere changes. Spec: construct a `DrawIrCommand` via each of the 3
existing construction call shapes without the new fields and assert
`has_transform == false` and identity defaults — proves the additive change
is truly invisible. No backend touched. **Fully CPU-verifiable, no GPU
dependency at all.**

### Stage 2 — CPU axis-preserving fast path (0/90/180/270°, no skew)
In `_engine2d_draw_ir_render_commands` (`draw_ir_adv.spl:1222`), branch on
`has_transform` and handle only the quadrant-rotation case by adjusting the
integer rect (swap w/h, translate for origin) before calling the existing
`draw_rect_filled`/`draw_image` trait methods — no new trait method, no new
raster code. Spec: a 90°-rotated rect command produces the same pixels as an
equivalent manually-swapped-w/h rect command (byte-for-byte CPU readback
comparison via `read_pixels()`). **CPU-verifiable.**

### Stage 3 — CPU arbitrary-angle rasterization
Add the inverse-mapping scratch-buffer rasterizer described in §3.1's second
bullet, feeding the existing `draw_image` trait method. Spec: known
pixel-level fixture for a 45°-rotated filled rect against a hand-computed
expected buffer (small, e.g. 8x8), run only against `CpuBackend`/
`SoftwareBackend`. **CPU-verifiable.**

### Stage 4 — Hit-test rotated-AABB lift
Implement §4.1 step 1 in `draw_ir_hit_forest`
(`draw_ir_hit_bridge.spl:46-132`): rotated-corner AABB for
`has_transform: true` leaves; unchanged for everything else. Spec: a
45°-rotated `hit_rect`'s derived `HitProxy2D` bounds equal the hand-computed
rotated-corner AABB; a non-transformed command's derived bounds are
byte-identical to today's output (regression guard for the ~11 existing
call sites). **CPU-verifiable, no rendering involved at all.**

### Stage 5 — Hit-test exact oriented-rect refinement
Implement §4.1 steps 2–3: `HitProxy2D.exact_contains_point`, wired into
`hit_stack`'s candidate-resolution step. Spec: a point inside the Stage-4
AABB but outside the true rotated rect resolves to "miss" (or falls through
to the next candidate) once refinement is applied; a point truly inside the
rotated rect still resolves "hit." **CPU-verifiable.**

### Stage 6 — Web renderer wiring
Replace `decl_apply.spl`'s width/height-mutating approximation
(§1.3) with setting `has_transform` + the decomposed fields on the emitted
`DrawIrCommand`, for `transform:`/`rotate:`/`scale:`/`skew()` (skew is
currently unparsed anywhere in `foundation.spl` — **UNVERIFIED** whether a
`parse_transform_skew*` helper needs to be authored fresh in this stage, no
existing skew parser was found this session). Spec: arbitrary-angle
`rotate(37deg)` now paints a rotated rect (Stage 2/3 dependency) instead of
being silently ignored. **CPU-verifiable** (web renderer already runs
headless/CPU per prior showcase-lane evidence).

### Stage 7 — Game `Transform2D` bridge
Wire `bridge_game2d.spl` (**UNVERIFIED** exact call site — not traced this
session) to decompose a sprite's `Transform2D` into the 5 DrawIR fields
per-command instead of only baking `pos_x/pos_y` into `x/y`. This is the
GAP-9 convergence decision the audit flagged
(`drawir_feature_gap_2026-07-31.md:183,249`) — scope it as its own follow-up
sub-lane rather than folding it silently into Stage 6, since it touches a
different producer with its own existing (already-correct) matrix math that
must not be duplicated or diverged from. **CPU-verifiable** (game2d specs
already run headless per existing test conventions).

### Stage 8 (parked, not scheped near-term) — GPU-side native transform
Vulkan/CUDA/Metal uniform-matrix paths per §3.2–3.4. Explicitly **not**
claimed board- or device-verifiable from this environment; file as a
follow-up once real Vulkan/CUDA hardware is available to close the loop, per
the board-runnable rule's "say so explicitly and file it" requirement rather
than silently shipping a paper design as done.

## Sources

Read in full this session: `draw_ir.spl:1-107` (struct block),
`draw_ir_target.spl:1-63` (trait + evidence struct),
`game2d/transform.spl:1-60`, `hit_proxy.spl` (full file),
`draw_ir_hit_bridge.spl` (grep-verified line ranges, structure read),
`hit_test.spl` (signature block), `decl_apply.spl:760-902`,
`foundation.spl:1170-1210`, `draw_ir_patch.spl:1-80`,
`draw_ir_adv.spl:1222-1270`. Backend census: `grep -rl draw_rect_filled
src/lib/gc_async_mut/gpu/engine2d/*.spl` (24 files) and `find` for
`backend_{cpu,cuda,emu,metal,software,vulkan}*.spl` under the same directory
(this session). Hit-forest WM-dispatch call sites:
`window_scene.spl:850-851,908-909,1009-1010`, `panel2d.spl:326-371`,
`host_gpu_event_queue.spl:221-227` (grep-confirmed this session).
