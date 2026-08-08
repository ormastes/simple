# GPU WebScene Offload — MDSOC+ Plan (experimental lane)

**Date:** 2026-07-31
**Status:** Proposed experimental plan
**Relationship to existing plan:** additive. `gpu_full_render_offload_mdsoc_plus_plan.md`
deliberately keeps semantics, events, parsing and layout on the CPU and remains the
conservative production plan. It and its SPipe lane must **not** be rewritten or
reinterpreted as already supporting GPU-owned web semantics.

**Structural-compute alignment:** this lane consumes the shared contracts defined in
`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`:

- `GpuWebScene` device pools are Object VM-managed arenas (Part VIII residency/placement/lease
  contracts — the "GPU MMU"); they must not grow a second, private placement layer;
- DOM/CSS invalidation frontiers use the DirtyMask + selector-feature model (§9.6) and
  `StyleDifference` classification, with full recomputation as the oracle;
- CSS selectors compile to QueryIR (§7.7); the GPU selector tables are an execution backend of
  that program form, not a separate selector language;
- the deterministic mutation journal commits through MutationIR snapshot semantics (§8):
  immutable scene generation in, validated plan, new generation out, receipt;
- DrawIR v3 tables carry `SourceProvenanceTable` entries expressed as MappingGraph edges
  (`PaintOf`, `HitRegionOf`) so paint/hit results trace to DOM/style/layout entities.
- DrawIR v3 is a packed, additive encoding of the one shared display list — DrawIR v2 /
  `DrawIrComposition` — not a second display-list format. The standing WebIR rejection
  (`doc/03_plan/ui/webir_drawir_optimization.md` §Decision) applies to v3 unchanged: v2 stays
  canonical and the v2/v3 adapters (Program 2, I9) are the only bridge.
- QueryIR shares its "declarative query → planned execution form" shape with the compiler's
  CollectionPlan IR (`doc/01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md`
  §4–§5); keep the two cost registries converged rather than growing a second op-cost table.

Per-lane parallel plans: `doc/03_plan/platform/structural_compute/`.

## Recommended direction

The right target for Simple is an additive GPU-resident WebScene lane, not a destructive replacement of the current renderer:

```text
existing production path:
CPU semantics/layout/event → DrawIR v2 → Engine2D → CPU/GPU backend

new experimental path:
thin CPU host → sealed input/effect packets → GPU WebScene
              → GPU event/script/style/layout
              → packed no-reallocation DrawIR v3
              → GPU raster/composition/present
```

A restricted subset of Simple script is well suited to GPU execution. The repository already has useful foundations:

- MIR GPU instructions, barriers, atomics and `HostGpuLaneBegin/End`.
- A ProcessingIR design that rejects recursion, GC, host pointers, unbounded loops, exceptions and other GPU-hostile features.
- A host/GPU queue, sealed DrawIR payloads and explicit completion receipts.
- A DrawIR-derived hit forest.
- CPU/GPU dual-algorithm and parity infrastructure.

But the compiler-to-GPU path is still largely a vertical slice rather than a complete script/event compiler, and the current DrawIR uses dynamic arrays and textual values rather than a no-reallocation packed representation.

---

## 1. Ideal CPU/GPU interaction

Initial page creation

```text
PROCESS / TIME ──────────────────────────────────────────────────────────────────────────────────────────────────────▶

CPU │ Network/file/IRQ → validate transport envelope → append sealed byte/resource packets ───────────────→ host effects / fault recovery
    │                                                    │
GPU │                                                    └→ HTML tokenize/tree → GPU DOM → CSS parse/index
GPU │                                                                              → selector match/cascade/var()
GPU │                                                                              → text/resource resolution
GPU │                                                                              → layout/fragments
GPU │                                                                              → count/scan/emit packed DrawIR
GPU │                                                                              → raster/effects/composite
GPU │                                                                              → direct present
```

Event-driven frame

```text
PROCESS / TIME ──────────────────────────────────────────────────────────────────────────────────────────────────────▶

CPU │ Device event → normalize → write event ring ─────────────────────────────────────────────────────────→ optional host-effect service
    │                              │
GPU │                              └→ validate scene generation → hit query → capture/target/bubble route
GPU │                                                                    → execute GPU-safe Simple handlers
GPU │                                                                    → deterministic mutation-journal commit
GPU │                                                                    → style/layout invalidation frontier
GPU │                                                                    → DrawIR patch/count/scan/emit
GPU │                                                                    → raster damage/composite/present
```

The CPU should not receive a full DOM, style tree, layout tree, DrawIR or pixel frame on the healthy path. It receives only small receipts such as:

```text
epoch completed
host effect requested
capacity overflow
unsupported feature
device fault
accessibility snapshot requested
```

Mainstream browsers currently stop GPU ownership much earlier: Chromium creates display lists from layout-side paint traversal; Firefox serializes a CPU-created WebRender display list to the GPU process; Servo owns DOM and script in its script thread and uses CPU layout workers before sending a display list to WebRender. These are robust references, but they do not demonstrate that the more aggressive Simple target is impossible.

---

## 2. GPU-offloadable Simple script

### Proposed language boundary

Introduce an additive, domain-specific function attribute:

```simple
@gpu_event(
    max_steps=256,
    max_mutations=8,
    max_host_effects=1,
    deterministic=true
)
fn on_button_click(
    ctx: GpuEventContext,
    mut out: GpuEventWriter
):
    if ctx.target_role == UI_ROLE_BUTTON:
        out.toggle_state(ctx.target_id, UI_STATE_PRESSED)
        out.set_class(ctx.target_id, CLASS_ACTIVE)
        out.invalidate(ctx.target_id, INVALIDATE_STYLE_PAINT)
```

This syntax does not exist yet; it is the proposed frontend surface.

The compilation route should be:

```text
Simple function
    → HIR effect and bound analysis
    → GpuEventIR
    → ProcessingIR
    ├─ CPU oracle
    ├─ Vulkan SPIR-V
    ├─ CUDA
    ├─ Metal MSL
    ├─ DirectX HLSL/DXIL
    └─ CPU SIMD
```

Simple already has the underlying MIR vocabulary for kernels, launches, thread IDs, barriers, shared storage and atomics, and its ProcessingIR design already defines most of the restrictions needed for this subset. The missing pieces are complete lowering, resource contracts and real backend execution for event programs.

### Suitable event/script operations

| Operation | GPU suitability | Proposed behavior |
|---|---|---|
| Hover, press, checked, selected state | Excellent | Direct mutation-journal record |
| Class/state token updates | Excellent | Numeric token IDs, no strings in hot path |
| Scroll-offset update | Excellent | Clamp and update GPU scene state |
| Transform, opacity, color animation | Excellent | Device-resident animation state |
| Focus candidate calculation | Good | GPU computes candidate; host services IME/accessibility |
| List filtering, sorting, selection | Excellent for large data | Bounded array operations |
| Form validation using fixed rules | Good | GPU-safe predicates and diagnostics |
| Timer-driven animation | Excellent | GPU timeline or frame epoch |
| Simple arithmetic and bounded loops | Excellent | ProcessingIR |
| Large hit/collision query | Excellent | Spatial grid/BVH or ID buffer |
| DOM class/attribute mutation | Good | Mutation records against stable node IDs |
| Subtree insertion from a compiled template | Good | Instantiate from precompiled blueprint |
| Arbitrary new markup string parsing | Possible but costly | Append input to GPU parser queue |
| Network request | Host effect | GPU emits `FetchRequest` |
| Clipboard | Host effect | GPU emits `ClipboardRequest` |
| File access | Host effect | GPU emits `FileRequest` |
| IME composition service | Host effect | OS-owned service |
| Accessibility OS API | Host effect | CPU publishes or consumes snapshots |
| Arbitrary FFI/syscall | Rejected | Not legal in `@gpu_event` |
| Runtime recursion | Rejected | Must be statically bounded or transformed |
| GC/heap allocation | Rejected | Fixed pools and bounded writers only |
| Exceptions/unwind | Rejected | Explicit result and fault codes |
| Arbitrary object identity/pointers | Rejected | Stable index plus generation only |

This follows the successful pattern used by data-parallel languages: Futhark deliberately restricts itself to statically typed data-parallel programs and compiles them to CUDA, OpenCL or multicore CPU; Taichi separates device kernels from host Python and restricts dynamic host objects and runtime recursion; GPU.js translates suitable JavaScript functions rather than trying to run unrestricted JavaScript objects on the GPU.

### Host effects are not full CPU fallback

A GPU handler that needs a system service should not abandon its entire event epoch:

```simple
@gpu_event(max_steps=128, max_mutations=4, max_host_effects=1)
fn on_load_clicked(ctx: GpuEventContext, mut out: GpuEventWriter):
    out.set_state(ctx.target_id, UI_STATE_LOADING, true)
    out.request_host(
        HOST_EFFECT_FETCH,
        ctx.bound_resource_id,
        continuation_id=CONTINUE_FETCH_RESULT
    )
```

Flow:

```text
GPU handler
    → commits local loading state
    → emits bounded HostEffectRequest

CPU host service
    → performs network/file/clipboard/IME operation
    → returns HostEffectCompletion event

GPU continuation
    → updates DOM/state
    → reruns invalidated style/layout/render stages
```

Only the actual OS effect crosses to the CPU. That is normal capsule interaction, not whole-render fallback.

---

## 3. GPU event model

### Event records

```simple
struct GpuInputEvent:
    sequence: u64
    scene_generation: u64
    timestamp_ns: u64

    kind: u16
    device_id: u16
    flags: u32

    x_fixed: i32
    y_fixed: i32
    delta_x_fixed: i32
    delta_y_fixed: i32

    key_code: u32
    text_offset: u32
    text_length: u32

struct GpuMutation:
    node_id: u32
    node_generation: u32
    field_id: u16
    operation: u16
    value_lo: u32
    value_hi: u32
    sequence: u32

struct GpuHostEffectRequest:
    event_sequence: u64
    effect_kind: u16
    continuation_id: u16
    payload_offset: u32
    payload_length: u32
```

Variable strings are stored in fixed event/payload arenas and referenced with offsets and lengths.

### Per-event execution

```text
1.  Validate event.scene_generation.
2.  Coalesce pointer-move/wheel events where legal.
3.  Hit-test against the immutable current scene generation.
4.  Build ancestor route from parent IDs.
5.  Execute capture listeners.
6.  Execute target listeners.
7.  Execute bubble listeners.
8.  Append bounded mutations and host-effect requests.
9.  Stable-sort or deterministically enumerate mutation records.
10. Commit a new scene generation.
11. Propagate invalidation frontiers.
12. Recompute only affected style, layout and DrawIR regions.
```

The deterministic order should be:

```text
event sequence
→ capture/target/bubble phase
→ route position
→ listener registration order
→ mutation sequence inside the listener
```

No mutation is applied directly while listeners are executing. Handlers write a transaction journal; one commit kernel applies it after all relevant handlers complete.

This avoids nondeterministic atomics becoming semantic ordering. Vulkan device-generated commands can execute device-produced work, but its explicitly unordered sequence mode is not guaranteed deterministic; Simple should use stable sequence buffers for event and UI execution.

### Hit testing

Simple already has the correct semantic starting point: `hit_rect`, `parent_id`, paint layer and emission order can be lifted from DrawIR into a shared hit forest. Today that bridge is CPU-side and its basic collision path is pairwise. Keep the contract but add a retained GPU index implementation rather than building another event model.

Recommended backends:

| Scene size/type | Hit backend |
|---|---|
| Small conventional GUI | CPU or one GPU warp; select by measured cost |
| Medium GUI/web scene | Uniform grid of node IDs |
| Large transformed web/canvas scene | GPU BVH or hierarchical grid |
| Pixel/mask-sensitive target | ID/picking buffer |
| Scrolling retained scene | Transform query against persistent index |
| SimpleOS without GPU | Same hit contract over CPU SIMD |

The current scheduler already recognizes a coarse `hit_query` and rejects per-widget GPU dispatch and GPU mutation of host semantics. Extend that policy rather than bypassing it.

---

## 4. Full GPU WebScene

### Device-resident stores

```text
GpuWebScene
├─ input byte ring
├─ token arena
├─ DOM node pool
├─ attribute/value pools
├─ string interning table
├─ selector/rule tables
├─ computed-style tables
├─ custom-property dependency graph
├─ layout box/fragment pools
├─ glyph-run tables
├─ decoded media-resource table
├─ event listener table
├─ hit index
├─ mutation journal
├─ DrawIR v3 arenas
├─ Prepared2D arenas
└─ epoch/fault/evidence receipts
```

All links use:

```text
index + generation
```

not host pointers or movable addresses.

### HTML and CSS stages

```text
compressed/input bytes
    → byte classification
    → tokenizer state summaries
    → prefix-state resolution
    → token output offsets
    → tree-construction operations
    → GPU DOM pools
```

GPU parsing is not merely theoretical. ParPaRaw demonstrates massively parallel FSM parsing without a preliminary sequential context pass, while Pareas implements a simple-language compiler entirely on a GPU, including parsing and code generation, and includes a GPU JSON parser and parallel lexer/parser generator. Those systems do not implement HTML5, but they validate the core techniques needed for GPU tokenization and parsing.

CSS processing:

```text
rule/token tables
    → selector candidate generation
    → selector verification
    → candidate cascade-key generation
    → stable segmented winner reduction
    → custom-property dependency graph
    → cycle/SCC detection
    → frontier-based substitution
    → typed computed styles
```

For small mutations, one GPU workgroup may be enough; for full-page recomputation, candidate matching, sorting and segmented reductions scale across the device. Earlier browser research demonstrated parallel selector and layout techniques, while Servo shows the practical multicore CPU version of parallel tree traversal. The proposed GPU version should retain the same serial/CPU oracle.

### Layout

Use specialized formatting-context kernels:

```text
classify formatting contexts
    → bottom-up intrinsic-size reduction
    → top-down containing-block propagation
    → block/flex/grid/table/absolute specialized kernels
    → inline shaping and line breaking
    → convergence/fixpoint frontier
    → fragment and clip pools
```

Do not put all CSS layout into one giant branch-divergent kernel. Use a device task graph with nodes such as:

```text
IntrinsicBlock
FlexMeasure
FlexDistribute
GridTrack
InlineShape
InlineBreak
TableMeasure
AbsolutePlace
TransformResolve
OverflowResolve
```

WGLog demonstrates that recursive/fixpoint work can remain inside a browser GPU path using sorted-array operations and indirect dispatch to avoid a host round-trip per iteration. Persistent-megakernel systems such as Mirage demonstrate a device scheduler and worker model that can eliminate repeated host launches, though their workload is very different from a web engine.

### Text

Initial production stage:

```text
CPU host text service:
    OpenType shaping and font fallback

GPU:
    glyph outline/bitmap rendering
    atlas or outline-blob cache
    composition
```

Long-term target:

```text
GPU:
    Unicode segmentation
    shaping plan execution
    GSUB/GPOS
    line breaking
    glyph outline raster
```

Current HarfBuzz GPU work encodes glyph outlines on the CPU and decodes/rasterizes them on the GPU; it is an excellent rendering reference but not yet a fully GPU-resident shaping engine.

---

## 5. Media offload

### Resource flow

```text
CPU transport:
    compressed bytes enter shared/pinned ring

GPU/media engine:
    parse/decode to device image
    → colorspace conversion
    → scaling
    → texture/resource table
    → DrawIR resource ID

CPU:
    no decoded-pixel round trip
```

### Format plan

| Format | Ideal target | Initial implementation |
|---|---|---|
| JPEG | GPU or fixed-function hardware | nvJPEG/platform codec; CPU oracle |
| JPEG 2000 | GPU codec | nvJPEG2000/plugin |
| WebP lossy | Vulkan/CUDA compute | VP8 entropy/reconstruct kernels |
| WebP lossless | Vulkan/CUDA compute | Prefix/LZ dependency analysis plus inverse transforms |
| PNG | Vulkan/CUDA compute | Inflate and filter kernels; CPU oracle |
| AVIF | Hardware AV1 where supported | Container parse plus device AV1 image |
| WebM VP9/AV1 | Vulkan Video/platform hardware | Zero-copy YUV device image |
| H.264/H.265 | Vulkan Video/platform hardware | Device decode and composition |
| SVG | GPU scene geometry | CPU oracle, GPU path/paint execution |
| GIF/APNG | Compute decode plus GPU frame composition | CPU oracle first |

WebP lossless is finite and well specified: prefix coding, LZ77 backward references, a color cache and predictor/color/subtract-green/index transforms. None requires a CPU in principle, but dependency discovery and wavefront reconstruction are needed for efficient parallel execution.

The maintained reference implementation is libwebp. I did not find a maintained, full-featured, browser-grade Vulkan/CUDA decoder covering lossy, lossless, alpha, animation and malformed-input validation. Therefore, a Simple GPU WebP implementation should be treated as a new codec project with libwebp as the bit-exact oracle — not as integration of an already mature library.

Vulkan Video already defines device decode profiles and parameters for VP9 and AV1, making it the appropriate route for compatible WebM video rather than writing those video codecs as ordinary compute shaders.

---

## 6. No-reallocation IR and scene memory

### Current problem

Current DrawIR v2 contains dynamic arrays and strings:

```text
batches[]
commands[]
computed_style[]
advance_widths[]
points[]
glyph IDs/positions/clusters[]
component_id text
parent_id text
image_uri text
```

The executor also scans and parses textual style values at execution time. This is not a suitable no-reallocation GPU-write format.

### Additive DrawIR v3

Do not replace v2. Add:

```simple
struct DrawIrV3Command:
    kind: u16
    flags: u16

    component_id: u32
    component_generation: u32
    parent_id: u32

    geometry_id: u32
    paint_id: u32
    text_run_id: u32
    image_resource_id: u32
    path_span_id: u32
    clip_id: u32
    transform_id: u32
    hit_shape_id: u32
```

Separate immutable tables:

```text
GeometryTable
PaintTable
TextRunTable
ResourceTable
PathPointTable
ClipTable
TransformTable
HitShapeTable
SourceProvenanceTable
```

The render-hot structures contain no text keys and no nested dynamic arrays.

### Capacity manifest

A finite no-reallocation system requires explicit policy bounds. Arbitrary untrusted web content is mathematically unbounded, so no finite memory reservation can cover every possible page without limits.

```simple
struct GpuWebCapacityManifest:
    max_input_bytes: u64

    max_nodes: u32
    max_attributes: u32
    max_dom_edges: u32
    max_string_bytes: u64

    max_css_rules: u32
    max_selectors: u32
    max_selector_candidates: u32
    max_computed_styles: u32
    max_custom_property_edges: u32

    max_layout_boxes: u32
    max_fragments: u32
    max_line_boxes: u32
    max_glyphs: u32

    max_events_in_flight: u32
    max_route_depth: u16
    max_mutations_per_epoch: u32
    max_host_effects_per_epoch: u32

    max_draw_batches: u32
    max_draw_commands: u32
    max_path_points: u32
    max_patch_operations: u32

    parser_scratch_bytes: u64
    style_scratch_bytes: u64
    layout_scratch_bytes: u64
    scan_scratch_bytes: u64
    backend_preprocess_bytes: u64
```

Sources for the manifest:

```text
compile time:
    GUI/theme recipes
    GPU-safe Simple handlers
    static HTML/CSS/templates

load time:
    response size and declared resource headers
    viewport/locale/font profile
    dynamic-content policy limits

backend session creation:
    alignment
    descriptor limits
    indirect/preprocess requirements
```

### Exact emission without realloc

```text
Kernel A: count output records per source item
Kernel B: exclusive prefix scan
Kernel C: verify total <= capacity
Kernel D: emit records into exact offsets
Kernel E: compact/cull/batch
```

Vello demonstrates the value of prefix-sum algorithms for moving ordering and clipping work to GPU compute. Vulkan device-generated commands also explicitly query preprocessing allocation requirements, which can be allocated once when the backend session is created.

### Stable paged pools

Do not require one physically contiguous mega-allocation:

```text
logical arena
    ├─ fixed page 0
    ├─ fixed page 1
    ├─ fixed page 2
    └─ ...
```

References are:

```text
page index + element offset
```

Existing records never move.

Three practical modes:

| Mode | Allocation behavior |
|---|---|
| Embedded/fixed GUI | Allocate exact maximum once |
| Typical desktop/web | Allocate fixed page pool and page table once |
| Large server/browser workload | Reserve several preallocated capacity tiers |

Overflow policy:

```text
1. Set overflow flag and required_count.
2. Do not write beyond bounds.
3. Discard incomplete candidate generation.
4. Keep presenting the last complete scene generation.
5. Switch at an epoch boundary to an already allocated larger tier, or reject.
6. Never `realloc` or move live records mid-frame.
```

In strict GPU mode, overflow is an explicit failure. In compatibility mode, a CPU path may render the affected document, but it must be reported as a full fallback — not hidden.

### Cross-startup cache

Persist:

```text
compiled theme recipes
parsed immutable DOM/CSS templates
GPU-safe script bytecode/AOT metadata
interned strings and selectors
capacity manifest
high-water measurements
packed DrawIR-independent resources
```

Cache key:

```text
schema version
compiler build hash
source/resource hashes
theme hash
locale
font manifest
viewport/scale class
GPU feature profile
```

Never persist:

```text
VkBuffer
MTLBuffer
D3D resource handles
CUDA pointers
descriptor-set handles
queue handles
```

Those are rebuilt within the backend capsule.

---

## 7. Minimizing CPU fallback

### Fallback hierarchy

| Level | Trigger | Response |
|---|---|---|
| L0: GPU-native | Supported epoch | All web/event/style/layout/render stages remain device-resident |
| L1: Host effect | File/network/clipboard/IME/accessibility | Execute only that effect on CPU; continue GPU scene |
| L2: Stage service | Unsupported text shaping or codec feature | CPU computes one bounded result and returns it as a resource |
| L3: Subtree compatibility | Unsupported CSS/layout feature | CPU produces one frozen subtree artifact; GPU composes it |
| L4: Document compatibility | Unsupported general JS or hard content profile | Existing CPU web path renders document |
| L5: Device recovery | Device lost/OOM/driver fault | Restart backend or use full CPU renderer |

Targets:

```text
supported Simple-Web GPU profile:
    L0 or L1 only

standards compatibility profile:
    L0–L3 accepted and reported

strict GPU verification:
    any L2–L5 occurrence fails the test

device failure mode:
    L5 allowed but never reported as GPU success
```

### Avoiding accidental fallback

1. Capability analysis happens before page admission.
2. Every CSS/layout/script/media feature has a numeric capability bit.
3. No backend may silently call `SoftwareBackend`.
4. CPU-oracle execution is test/shadow mode, not production frame generation.
5. Production presentation avoids full pixel readback.
6. GPU results return compact hashes/receipts, not framebuffer copies.
7. Small jobs may intentionally route to CPU by cost policy, but that is recorded as `cpu_selected`, not `gpu_fallback`.
8. GPU event dispatch is one event batch or epoch, never one submission per widget.

Current Simple already encodes several of these rules — coarse GPU batches, explicit host semantic ownership, packet limits and fallback evidence — but needs to extend them from DrawIR submission to the entire GPU WebScene pipeline.

---

## 8. Research and implementation references

| System | What it proves | Direct lesson for Simple |
|---|---|---|
| Chromium RenderingNG | Retained display lists, paint chunks, tiled GPU compositing | Retain scene artifacts and avoid full-frame reraster |
| Firefox WebRender | Self-contained display-list blob, GPU-process scene/frame, APZ event fast path | Versioned sealed IR and restartable GPU service |
| Servo | Script/DOM owner plus parallel layout workers and WebRender | CPU oracle architecture and parallel layout corpus |
| ParPaRaw | Parallel FSM parsing without a sequential context pass | HTML/CSS tokenizer summaries plus prefix-state composition |
| Pareas | Full compiler, parser and code generation on GPU | GPU parser/compiler stages are practical for restricted languages |
| Futhark | Restricted functional data-parallel language to CUDA/OpenCL/CPU | Model for GPU-safe Simple effect/type subset |
| Taichi | Explicit host scope versus device-kernel scope | Model for `@gpu_event` restrictions and diagnostics |
| GPU.js | Translating suitable JS-like functions to GPU execution | Usability reference, not semantic model |
| WGLog | Recursive/fixpoint WebGPU work with indirect dispatch and little host synchronization | Custom-property and layout-frontier evaluation |
| Mirage persistent kernel | GPU-local scheduler/worker megakernel | Optional CUDA persistent event/scene tier |
| Vello | GPU compute 2D using prefix scans | DrawIR count/scan/emit and compute raster |
| Vulkan DGC | Device-produced draw/dispatch command streams and queried preprocess memory | GPU-generated frame execution |
| Metal indirect command buffers | GPU-encoded draw command buffers | Metal implementation of generated DrawIR work |
| D3D12 Work Graph sample | GPU-created dynamic work graph | DirectX event/style/layout task scheduling |
| HarfBuzz GPU | CPU-encoded glyph outlines rasterized directly on GPU | Practical intermediate text-rendering stage |
| Vulkan Video | Device video decode profiles such as VP9 and AV1 | Zero-copy WebM/video resources |
| libwebp/WebP specification | Complete reference behavior and finite decoding rules | CPU oracle for a new GPU WebP decoder |

The production-browser references support retaining the existing CPU path as an oracle and recovery path. The parser/compiler and persistent-kernel references support the experimental device-resident path.

---

## 9. MDSOC+ capsule model

```text
HostPlatformCapsule
├─ InputPort
├─ NetworkPort
├─ StoragePort
├─ Clipboard/IME/AccessibilityPort
└─ FaultRecoveryPort

GpuWebServiceCapsule
├─ GpuIngressCapsule
├─ GpuDomCapsule
├─ GpuStyleCapsule
├─ GpuLayoutCapsule
├─ GpuEventCapsule
├─ GpuScriptCapsule
├─ GpuMediaCapsule
├─ GpuDrawIrCapsule
├─ GpuRenderCapsule
└─ GpuEvidenceCapsule
```

### Stable ports

```text
GpuInputPacketPort
GpuResourcePacketPort
GpuHostEffectRequestPort
GpuHostEffectCompletionPort
GpuSceneEpochPort
GpuPackedDrawPort
GpuMediaSurfacePort
GpuFaultReceiptPort
GpuDebugSnapshotPort
```

### Visibility rules

| Item | Visibility |
|---|---|
| Event and mutation packet schemas | Shared public contract |
| Stable node/resource IDs | Shared public contract |
| Scene generation and receipt schemas | Shared public contract |
| Packed DrawIR v3 schema | Shared public contract |
| DOM/style/layout pools | Private to `GpuWebServiceCapsule` |
| GPU scheduler state | Private |
| Vulkan/Metal/D3D/CUDA handles | Backend-private |
| Compiler internal HIR/MIR | Compiler-private |
| CPU oracle internals | Evidence/test capsule |
| Cross-startup cache encoding | Shared versioned contract |
| Cache storage policy | Platform-private |

MDSOC owns the outer service/capsule boundaries, ports, capabilities and fault containment. Retained ECS/SoA-like state is permitted inside `GpuWebServiceCapsule`; it must not leak into sibling capsules or become a replacement for the MDSOC ownership model.

The "plus" layer should contain:

```text
offline compiler
theme/script preprocessor
capacity-manifest generator
cache builder
CPU oracle
parity/fuzzing tools
trace and evidence generator
```

These tools support the runtime but do not own its live state.

---

## 10. Parallel-development isolation rules

Before implementation, create one ownership ledger:

```text
doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn
```

Each agent gets a dedicated branch and worktree.

### Mandatory rules

1. Each agent may modify only its assigned path prefixes.
2. Shared contracts are frozen before parallel implementation starts.
3. A contract change requires a new schema version; no agent edits a frozen contract in place.
4. Only integration agents may edit existing production entrypoints.
5. No implementation agent deletes, renames or moves an existing file.
6. Feature flags default to off.
7. Existing DrawIR v2, CPU event reducer and web renderer remain usable.
8. Every accelerated operation has a CPU oracle.
9. No backend reports success after an implicit software fallback.
10. Each agent owns its own tests and must not edit another group's tests.
11. Generated documentation is updated only by the evidence/documentation group.
12. No shared "utility" file may be created ad hoc; cross-group utilities require a frozen port or move to the owning capsule.

### Contract freeze group C0

This group runs before both implementation programs.

Owned paths:

```text
doc/04_architecture/ui/gpu_web_scene_ports.md
doc/05_design/ui/gpu_web_scene_contracts.md
doc/03_plan/agent_tasks/gpu_web_scene/ownership.sdn

src/lib/common/ui/gpu_web_ports.spl
src/lib/common/ui/gpu_web_capacity_contract.spl
src/lib/common/ui/gpu_web_receipt_contract.spl
src/lib/common/ui/draw_ir_v3_ports.spl
```

Deliverables:

```text
schema/version constants
stable IDs
input/effect/receipt packets
capacity-manifest contract
PackedDrawPort
CPU-oracle port
backend capability bitset
```

After C0 is merged, these files are read-only until an explicit schema-version change.

---

## 11. Program 1 — Full web rendering and event GPU offload

### W1 — GPU-safe Simple script compiler

Owned paths

```text
src/compiler/20.hir/gpu_event/
src/compiler/50.mir/gpu_event/
src/compiler/60.processing_ir/gpu_event/
src/compiler/70.backend/backend/processing/gpu_event/
test/01_unit/compiler/gpu_event/
```

Tasks

- Parse and validate `@gpu_event`.
- Effect analysis and bounded-loop proof.
- Reject heap/GC, recursion, exceptions, virtual dispatch, host pointers and unbounded output.
- Lower UI reads to immutable scene accesses.
- Lower writes to `GpuMutationWriter`.
- Lower OS interactions to `GpuHostEffectRequest`.
- Generate CPU oracle and ProcessingIR from the same HIR.
- Generate an AOT handler table or compact GPU bytecode.
- Emit capacity contributions per handler.

Acceptance

```text
same handler AST produces CPU and GPU programs
mutation journal is byte-identical
compile-time rejection includes exact unsupported construct
zero implicit allocations
bounded instruction/mutation/effect counts verified
```

Forbidden

```text
no browser renderer edits
no DrawIR implementation edits
no backend runtime edits outside its owned compiler directory
```

---

### W2 — GPU event core

Owned paths

```text
src/lib/common/ui/gpu_event/
src/lib/nogc_async_mut/gpu/engine2d/gpu_event/
test/01_unit/lib/common/ui/gpu_event/
```

Tasks

- Input ring.
- Event coalescing.
- GPU hit-query interface.
- Capture/target/bubble route.
- Listener table.
- Deterministic mutation journal.
- Host-effect request ring.
- Scene-generation and stale-event rejection.
- Pointer capture and focus-candidate state.
- CPU reference event interpreter.

Acceptance

```text
event route equals current CPU event semantics for selected corpus
stale generation never mutates state
same event batch produces deterministic mutation bytes over 1,000 repetitions
one coarse submission per event epoch
no per-widget GPU dispatch
```

---

### W3 — GPU HTML/CSS ingest and GPU DOM

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/ingest/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/dom/
test/01_unit/lib/gpu_web/ingest/
```

Tasks

- Parallel byte classification.
- HTML tokenizer state summaries.
- Prefix-state composition.
- Token offset counting/scan/emission.
- HTML insertion-mode and tree-operation representation.
- Fixed node/attribute/string pools.
- CSS tokenizer/parser into typed tables.
- DOM mutation operations by index plus generation.
- WPT-derived CPU/GPU comparison corpus.

Acceptance

```text
token and DOM serialization equals CPU oracle
malformed-input errors are deterministic
all writes are capacity checked
no pointer or array relocation
streaming chunks preserve parser state
```

---

### W4 — GPU selector, cascade and custom properties

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/style/
test/01_unit/lib/gpu_web/style/
```

Tasks

- Tag/class/id/attribute selector indexes.
- Selector candidate generation.
- Pseudo-state inputs.
- Stable cascade-key reduction.
- Inheritance environment IDs.
- Custom-property dependency graph.
- Cycle/SCC detection.
- `var()` fallback substitution.
- Precise invalidation frontiers.
- Typed paint/layout property output.

Acceptance

```text
specified/computed values equal CPU oracle
origin/layer/important/specificity/source-order cases covered
custom-property cycles and fallbacks match
paint-only changes do not force layout
selector candidate overflow fails closed
```

---

### W5 — GPU layout and text

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/text/
test/01_unit/lib/gpu_web/layout/
```

Tasks

- Formatting-context classification.
- Block, flex, grid and absolute kernels.
- Bottom-up intrinsic size and top-down constraints.
- Fragment generation.
- Overflow/scroll geometry.
- GPU line breaking for initial supported scripts.
- Host shaping-service adapter for unsupported scripts.
- Later GPU shaping table executor.
- Layout invalidation frontier.

Acceptance

```text
geometry and line boxes equal CPU oracle for admitted features
unsupported formatting context reported before execution
incremental update visits only invalidated frontier
fixed maximum iterations or explicit non-convergence fault
```

---

### W6A — GPU image codecs

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/media/image/
test/01_unit/lib/gpu_web/media/image/
```

Tasks

- Typed compressed-image resource contract.
- GPU WebP lossy and lossless staged decoder.
- GPU PNG inflate/filter staged decoder.
- JPEG/JPEG2000 backend adapters.
- Alpha, color-space and orientation handling.
- libwebp and CPU decoder oracle.
- Fuzzed malformed-input corpus.
- Fixed scratch-buffer formulas from headers and policy caps.

Acceptance

```text
bit-exact or specified-tolerance pixel parity
no decoded pixels cross GPU→CPU in production path
simple, alpha, lossless and lossy WebP separately gated
animation remains unsupported until its own gate
strict GPU mode rejects rather than silently CPU-decodes
```

---

### W6B — GPU video/media surfaces

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/media/video/
test/01_unit/lib/gpu_web/media/video/
```

Tasks

- WebM demux packet contract.
- Vulkan Video VP9/AV1 adapter.
- Metal VideoToolbox adapter.
- DirectX video adapter.
- CUDA/NVDEC adapter where useful.
- Zero-copy YUV device image.
- GPU color conversion and composition.
- Frame timing and drop policy.

---

### W7 — GPU WebScene scheduler

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/frame/
src/lib/nogc_async_mut/gpu/browser_engine/gpu_web/scheduler/
test/01_unit/lib/gpu_web/frame/
```

Tasks

- Stage dependency graph.
- Initial-load and event-epoch scheduler.
- Dirty-frontier propagation.
- Count/scan/emit invocation.
- Scene-generation publish.
- Resource lifetime and generation tracking.
- No-readback presentation contract.
- Optional portable frame-batch scheduler.
- Optional persistent/device-generated tier.

Backend scheduling tiers:

```text
Tier 0: portable explicit compute passes
Tier 1: indirect dispatch/draw
Tier 2: Vulkan device-generated commands
Tier 2: Metal indirect command buffers
Tier 2: D3D12 Work Graphs
Tier 2: CUDA persistent kernel/device graph
```

---

### W8V/W8M/W8D/W8C/W8W — platform scheduler adapters

| Group | Owned path | Scope |
|---|---|---|
| W8V | `.../gpu_web/backend/vulkan/` | Compute stages, indirect/DGC, timeline sync |
| W8M | `.../gpu_web/backend/metal/` | Compute stages, ICB, command events |
| W8D | `.../gpu_web/backend/directx/` | Compute stages, Work Graph/indirect execution |
| W8C | `.../gpu_web/backend/cuda/` | Persistent event scheduler, CUDA graphs |
| W8W | `.../gpu_web/backend/webgpu/` | Portable compute/indirect browser route |

These groups implement only the GPU WebScene scheduler adapter. Generic DrawIR v3 raster backends are owned by Program 2.

---

### W9 — host services and SimpleOS bridge

Owned paths

```text
src/lib/gc_async_mut/gpu/browser_engine/gpu_web/host/
src/os/lib/gpu_web_bridge/
test/01_unit/os/gpu_web_bridge/
```

Tasks

- OS event normalization.
- Shared/pinned packet rings.
- File/network/clipboard/IME/accessibility effect services.
- Device fault and restart.
- SimpleOS IVSHMEM transport.
- Cross-process sandbox.
- Tiny receipt propagation.

---

### W10 — Web integration agent

This is the only Program 1 group allowed to edit existing browser entrypoints.

Owned existing files

```text
src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl
src/app/ui.browser/backend.spl
src/app/ui.browser/backend*.spl only when explicitly listed in ownership.sdn
```

Feature flags

```text
SIMPLE_WEB_GPU_SCENE=0
SIMPLE_GPU_EVENT_SCRIPT=0
SIMPLE_WEB_GPU_STRICT=0
SIMPLE_WEB_GPU_SHADOW=0
```

Integration stages

```text
flag off:
    existing behavior byte-identical

shadow:
    current CPU result remains authoritative
    GPU scene runs and compares receipts/IR/pixels

candidate:
    GPU authoritative for admitted fixtures
    CPU path retained for recovery

promotion:
    GPU default only after parity/perf/fault gates
```

---

### W11 — Program 1 evidence

Owned paths

```text
test/03_system/gpu_web_scene/
test/05_perf/gpu_web_scene/
doc/06_spec/03_system/gpu_web_scene/
doc/09_report/gpu_web_scene/
scripts/check/check-gpu-web-scene-*.shs
```

No implementation edits.

---

## 12. Program 2 — IR optimization and non-destructive refactoring

### I1 — DrawIR v3 contract

Owned paths

```text
src/lib/common/ui/draw_ir_v3/contract/
test/01_unit/lib/common/ui/draw_ir_v3/contract/
```

Define:

```text
fixed numeric commands
typed table IDs
stable scene/component IDs
source-provenance side table
versioned binary ABI
PackedDrawPort
```

DrawIR v2 remains unchanged.

---

### I2 — Capacity and no-reallocation pools

Owned paths

```text
src/lib/common/ui/draw_ir_v3/capacity/
src/lib/nogc_async_mut/gpu/engine2d/draw_ir_v3/arena/
test/01_unit/lib/common/ui/draw_ir_v3/capacity/
```

Tasks:

```text
capacity-manifest generation
fixed/paged arena
checked count arithmetic
epoch reset
triple-buffer generations
overflow receipt
high-water telemetry
debug guards/poisoning
```

Acceptance:

```text
zero allocator calls after scene/session seal
zero record relocation
guard region unchanged
overflow never writes beyond bound
```

---

### I3 — Typed paint, text and resources

Owned paths

```text
src/lib/common/ui/draw_ir_v3/paint/
src/lib/common/ui/draw_ir_v3/text/
src/lib/common/ui/draw_ir_v3/resource/
```

Replace runtime string parsing with typed values:

```text
solid/linear/radial/image paint
typed borders and radii
typed shadows/filters
blend modes
transforms
clip/mask operations
resolved text-run IDs
device-independent resource IDs
```

---

### I4 — Full incremental diff/patch/damage

Owned paths

```text
src/lib/common/ui/draw_ir_v3/patch/
test/01_unit/lib/common/ui/draw_ir_v3/patch/
```

Current DrawIR patching is library-only, single-batch and does not compare every command field. V3 must support multi-batch insert/remove/update/reorder, full-field equality, resource updates and effect-expanded damage.

---

### I5 — CPU oracle and validation sink

Owned paths

```text
src/lib/nogc_async_mut/gpu/engine2d/draw_ir_v3/cpu_oracle/
src/lib/common/ui/draw_ir_v3/validate/
```

Implement from one canonical operation walker:

```text
CountingSink
ArenaSink
ValidationSink
HashSink
CPUPrepared2DSink
```

This prevents estimator/renderer drift.

---

### I6 — GPU count/scan/emit and Prepared2D

Owned paths

```text
src/lib/nogc_async_mut/gpu/engine2d/draw_ir_v3/gpu_prepare/
src/lib/common/ui/prepared2d/
```

Tasks:

```text
per-fragment cost
exclusive scan
packed emission
culling
batch classification
instance/path/glyph buffers
indirect command records
no host readback
```

---

### I7 — retained hit/event index

Owned paths

```text
src/lib/common/ui/draw_ir_v3/hit/
src/lib/nogc_async_mut/gpu/engine2d/draw_ir_v3/hit/
```

This owns the generic DrawIR v3 hit index. Program 1's event core only consumes its port.

---

### I8 — frozen artifact and cross-startup cache

Owned paths

```text
src/lib/common/ui/draw_ir_v3/cache/
src/app/ui.cache/draw_ir_v3/
```

Tasks:

```text
portable frozen blobs
hash/version/dependency manifest
mmap validation
internal offset checking
cache invalidation
no raw backend handles
```

---

### I9 — v2/v3 compatibility adapters

Owned paths

```text
src/lib/common/ui/draw_ir_v3/compat/
test/01_unit/lib/common/ui/draw_ir_v3/compat/
```

Adapters:

```text
v2 → v3
v3 → diagnostic v2
v3 → SDN/debug JSON
v2/v3 semantic checksum
```

No changes to v2 schema.

---

### I10V/I10M/I10D/I10C/I10S — generic execution backends

| Group | Owned path | Responsibility |
|---|---|---|
| I10V | `.../draw_ir_v3/backend_vulkan/` | Vulkan Prepared2D execution/direct present |
| I10M | `.../draw_ir_v3/backend_metal/` | Metal execution/direct present |
| I10D | `.../draw_ir_v3/backend_directx/` | DirectX execution/direct present |
| I10C | `.../draw_ir_v3/backend_cuda/` | CUDA compute renderer/interoperation |
| I10S | `.../draw_ir_v3/backend_simd/` | CPU SIMD oracle and fallback |

All consume the same Prepared2D contract.

---

### I11 — Engine2D integration agent

Only this group may edit:

```text
src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl
src/lib/gc_async_mut/gpu/engine2d/engine.spl
src/lib/gc_async_mut/gpu/engine2d/mod.spl
```

Additive entries:

```text
engine2d_draw_ir_v3_*
engine2d_prepared2d_*
```

Existing v2 functions and behavior remain.

---

### I12 — Program 2 evidence

Owned paths

```text
test/03_system/draw_ir_v3/
test/05_perf/draw_ir_v3/
doc/06_spec/03_system/draw_ir_v3/
doc/09_report/draw_ir_v3/
scripts/check/check-draw-ir-v3-*.shs
```

---

## 13. Parallel execution waves

```text
WAVE 0 ─────────────────────────────────────────────────────────────────────────────────────────────▶
C0 contract and ownership freeze
CPU baseline hashes, current perf, current fallback counts

WAVE 1 ─────────────────────────────────────────────────────────────────────────────────────────────▶
Program 1: W1 script compiler, W2 event core
Program 2: I1 contract, I2 arenas, I3 typed tables

WAVE 2 ─────────────────────────────────────────────────────────────────────────────────────────────▶
Program 1: W3 ingest/DOM, W4 style, W5 layout/text, W6 media
Program 2: I4 patch, I5 CPU oracle, I6 GPU preparation, I7 hit, I8 cache, I9 adapters

WAVE 3 ─────────────────────────────────────────────────────────────────────────────────────────────▶
Program 1: W7 scheduler, W8* platform scheduler adapters, W9 host bridge
Program 2: I10* rendering backends

WAVE 4 ─────────────────────────────────────────────────────────────────────────────────────────────▶
W10 and I11 integration in separate existing-file scopes
Shadow execution only

WAVE 5 ─────────────────────────────────────────────────────────────────────────────────────────────▶
W11/I12 system tests, fault tests, performance gates
Candidate promotion by backend and feature family
```

Dependency graph:

```text
                             ┌→ W1 script ───────────────┐
C0 contracts ────────────────┼→ W2 events ───────────────┤
                             ├→ W3 DOM → W4 style → W5 layout ─┐
                             └→ W6 media ───────────────────────┤
                                                                ▼
I1 contract → I2 arena → I3 tables → I6 PackedDraw/Prepared2D → W7 scheduler
                   ├→ I4 patch ────────────────────────────────┤
                   ├→ I7 hit ───────────────→ W2 event core ───┤
                   ├→ I8 cache ─────────────────────────────────┤
                   └→ I9 compatibility ─────────────────────────┘
                                                                ▼
                                          W8* scheduler + I10* render backends
                                                                ▼
                                              W10/I11 feature-gated integration
```

---

## 14. Acceptance gates

### Functional parity

| Gate | Required evidence |
|---|---|
| Script | CPU and GPU mutation journals byte-match |
| Events | Same target and capture/target/bubble order |
| HTML | Token and DOM canonical serialization match |
| CSS | Matched rules, cascade winners and computed values match |
| Custom properties | Cycle/fallback results match |
| Layout | Geometry, fragments, line boxes and overflow match |
| DrawIR | V2-adapted and v3 semantic checksums match |
| Media | Pixel or codec-defined tolerance parity |
| Rendering | CPU oracle and GPU capture parity |
| Cache | Cold result equals cross-startup cached result |

### Memory safety

```text
zero realloc after scene seal
zero hot-path allocator calls
all count/multiply operations checked
all spans validated
all generation IDs validated
all capacity overflows fail closed
no untrusted cached offset accepted without bounds checking
```

### CPU/GPU boundary

```text
one coalesced input packet per epoch
no per-widget submissions
no full DOM/style/layout/DrawIR readback
no production pixel readback
only bounded host-effect and fault receipts
```

### Fallback

```text
strict admitted corpus:
    full CPU fallback count = 0
    stage CPU fallback count = 0
    hidden SoftwareBackend calls = 0

compatibility corpus:
    every fallback has feature ID, subtree/document ID and reason

device fault:
    no false GPU success receipt
```

### Performance

Promotion requires measured improvement, not an assumed GPU advantage:

```text
GPU p50 and p95 event-to-present no worse than CPU baseline
offload transfer + synchronization included
small-workload routing separately measured
scene-resident repeated events show near-zero CPU render work
capacity high-water and wasted memory reported
```

---

## 15. First shippable vertical slice

Do not begin with the full HTML5 parser or complete WebP decoder. The first end-to-end slice should use a compiled Simple Web fixture containing:

```text
panel
button
checkbox
textfield
scroll area
CSS custom property
hover/pressed/focus states
flex row
one predecoded image
```

Process:

```text
CPU │ pointer/key event → normalized event packet ───────────────────────────────────────────────────────▶ receipt only
GPU │                 → hit → @gpu_event → mutation journal → cascade/var()
GPU │                                              → incremental flex/layout
GPU │                                              → DrawIR v3 count/scan/emit
GPU │                                              → Vulkan Prepared2D
GPU │                                              → direct present
```

Required proof:

```text
no allocator/reallocator call after startup
no pixel readback
no per-widget GPU submission
no CPU semantic handler on admitted events
CPU oracle state/layout/IR/pixel parity
device loss cleanly falls back or restarts
feature flag off remains byte-identical to current behavior
```

After that slice is stable, add in order:

1. GPU HTML/CSS ingestion
2. larger selector/cascade corpus
3. grid/inline layout
4. GPU image decoding
5. GPU video surfaces
6. complex text shaping
7. dynamic GPU DOM templates
8. broader Simple GPU script

The crucial implementation ordering is therefore:

> Build the versioned, typed, no-reallocation DrawIR v3 foundation first; develop the GPU-safe Simple event compiler and event transaction model alongside it; only then connect full GPU DOM/style/layout/media stages.

That ordering preserves every existing Simple rendering and event path, gives all agent groups disjoint ownership, and makes each promoted GPU feature independently measurable and reversible.
