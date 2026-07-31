<!-- codex-design -->
# Draw IR + Web/GUI Engine2D Reconciliation Plan (2026-07-31)

Status: active. Production still uses `simple-draw-ir-v2`; the additive
`simple-draw-ir-v3` flat SoA contract and CPU-reference A-E emitter exist, but
have no production producer or Engine2D executor. This plan reconciles those
schemas, Web/GUI producers, Engine2D execution, and GPU backend evidence. It
supersedes completion claims in older plans where this file is more specific.

## Invariant

Production Web and GUI producers lower through their semantic/layout owners to
`DrawIrComposition`. One retained Engine2D owner executes that composition.
Draw IR text reaches `draw_text` and transient `FontRenderer`/
`FontRenderBatch` state; atlas/cache material never enters Draw IR. CPU pixels,
private bitmap text, heuristic scenes, and readback are compatibility,
diagnostic, or recovery paths, never alternate canonical producers.

## Audited State

| Surface | Current evidence | Status |
|---|---|---|
| Web semantic/layout -> Draw IR | HTML layout emits explicit document-root parent and hit metadata plus image commands | source/spec ready; execution blocked |
| Widget -> Draw IR | canonical commands carry parent/hit metadata; unchanged frames use session-owned retained composition storage | source/spec ready; execution blocked |
| WM events | pointer-down and wheel traverse the same interaction ancestry | source/spec ready; execution blocked |
| `ui.browser` | submits the supplied composition to `engine2d_draw_ir_adv_composition`; diagnostic pixels remain explicit recovery only | source/spec ready; execution blocked |
| Web session lifecycle | `BrowserBackend` owns one Engine2D and retained widget storage; shutdown is idempotent | source/spec ready; execution blocked |
| Iframes | inert `srcdoc` can flatten through `draw_ir_embed_composition`; five legacy pixel callers remain | partial |
| Draw IR v3 | flat SoA contract and bounded CPU-reference A-E emission exist; no production producer/executor | partial, not canonical |
| Draw IR execution | RECT/TEXT/IMAGE execute; EDGE/PATH/GROUP/PORT return typed rejection | source/spec ready; execution blocked |
| Text | canonical Draw IR reaches Engine2D shaping/batch execution | implemented |
| Hosted GUI/Metal text | private bitmap/glyph paths are compatibility-only and producer guards reject them as canonical evidence | source/spec ready; execution blocked |
| Vulkan batching | consecutive opaque rectangles use the rect-list boundary; physical Draw IR receipt is missing | source ready; live row open |
| CUDA/Metal batching | pending resources/primitives flush at batch boundaries; physical receipts are missing | source ready; live rows open |
| Region readback | strict `RequireDeviceRegion` fails closed unless the backend reports device-region readback | source/spec ready; live row open |
| Web GPU proof | no fresh complete Linux/macOS R9 matrix | blocked |

## Ordered Work

### R1. Production composition cutover

- Make `ui.browser.render_frame_with_composition` consume the supplied GUI/Web
  `DrawIrComposition`; remove the ignored-composition behavior.
- Put one persistent Engine2D owner in the browser session/runtime lifecycle.
  Request helpers borrow it; only session shutdown releases it.
- Keep software pixels only behind an explicit diagnostic/recovery mode.
- Acceptance: a system spec proves the supplied composition reaches the shared
  executor, two frames retain one owner/session generation with one initialization
  and one final shutdown, and no HTML reparse/private pixel artifact occurs on the
  composition path.

### R2. Event and producer metadata completion

- Route wheel records through `PointerEvent2D` and the interaction core into
  the owning scroll consumer.
- Populate stable `parent_id` and `hit_rect` in widget and remaining WM
  constructors; reject batch-level fallback IDs in canonical producer tests.
- Acceptance: pointer-down and wheel target the same component ancestry; WM,
  widget, and web compositions retain non-empty parent chains.

### R3. Iframe embedding

- Keep the implemented inert `srcdoc` batch flattening and migrate the five
  remaining child pixel render/blit callers to it after exact parity.
- Preserve the pixel path only as a parity oracle until exact corpus parity
  passes, then make it diagnostic-only.
- Existing static spec/manual evidence proves nested batches, clipping, parent
  IDs, ordering, and fail-closed admission. Acceptance still requires a
  qualified pure-Simple execution plus exact CPU-reference parity for each
  migrated caller; child script/network/input authority remains a separate RED
  security lane.

### R4. Canonical text enforcement

- Classify hosted GUI 5x7 and Metal direct glyph paths as compatibility-only,
  or delete them after required baremetal probes gain canonical coverage.
- Add negative guards proving Web/GUI producers cannot call private glyph
  raster/blit helpers.
- Acceptance: Draw IR TEXT reaches `draw_text`; each enabled vector-font draw
  uses transient `FontRenderer`/`FontRenderBatch` material, while bitmap-default
  text creates none. No producer serializes atlas/cache state.

### R5. Schema/executor coverage

- Use **schema-admitted** for RECT/TEXT/EDGE/PATH/IMAGE/GROUP/PORT.
- Add shared-executor behavior or typed fail-closed rejection for EDGE, PATH,
  GROUP, and PORT. Do not count schema constants as rendering.
- Add command-kind coverage to software first, then GPU parity where meaningful.
- Keep v2 as the production oracle until a typed v2/v3 adapter, the shared
  Engine2D v3 executor, and exact parity evidence all land. The v3 contract and
  CPU emitter alone do not authorize producer cutover.

### R6. Producer allocation work

- Remove widget traversal array copies and web `[canvas] + commands` rebuilding
  using existing mutable/capacity-aware collection patterns.
- Measure allocations and frame time on 64/1K/10K-command compositions; retain
  medians and max RSS.
- Adopt Draw IR diff/patch only if retained whole-frame reuse is insufficient.

Current candidate state: `WidgetDrawIrStorage` retains an unchanged canonical
composition in the browser session and rebuilds on root, viewport, backend,
widget revision, or theme identity change. The focused receipt requires one
build and one reuse at 64/1K/10K commands. Allocation/capacity identity and
fresh timing/RSS artifacts remain open because the admitted self-hosted runtime
exposes no authoritative counter and the current test runner is not admitted.

### R7. Backend capability completion

| Backend | Submission work | Required evidence |
|---|---|---|
| Vulkan | pack compatible primitives and reduce per-primitive dispatch | physical exact readback, counters, warm latency/RSS |
| CUDA | real `submit_batch`, retained allocations/module/session, no per-op sync | physical exact readback, stable identity, counters, warm latency/RSS |
| Metal | real command-buffer batch and retained buffers/pipelines | macOS exact readback, registry ID, counters, warm latency/RSS |
| Software/CPU-SIMD | executable oracle, not strict-GPU fallback | exact parity and explicit provenance |

Audited bounded lanes (2026-07-31):

- CUDA already retains its session/module/framebuffer and launches ordinary
  primitives asynchronously. Queue image source allocations until
  `submit_batch`, synchronize once, then release; prove two images have zero
  pre-submit and one post-submit sync with exact device readback. Apply the same
  pending-resource model to vector-font quads; R7 remains open while either
  image or font submission synchronizes per operation.
- Vulkan: pack consecutive opaque filled-rectangle records into one SSBO
  dispatch; retain current IMAGE/font/mask/fallback flush boundaries. Prove
  clear plus two rectangles drops from three accepted dispatches to two.
- Metal: retain primitive command encoding until `submit_batch`; flush before
  image, text, auxiliary, readback, and shutdown paths. Host-independent source
  contracts precede the macOS registry-ID/counter/parity receipt.

### R8. Device-region readback and fallback policy

- Implement backend-owned region readback where supported; host cropping is an
  API seam, not an optimization result.
- Eliminate silent `cpu_fallback` from strict production presentation. Strict
  GPU requests fail closed; diagnostic recovery is explicit and reported.
- Acceptance: live receipts distinguish device-region, full-device, and
  host-crop paths.

### R9. Live matrix

- Linux: software oracle, CPU-SIMD, physical CUDA, and physical Vulkan.
- macOS: physical Metal; Linux `metal-unavailable` proves fail-close only.
- Physical GPU rows require device-origin pixels, positive stable identity,
  exact checksum/parity, no CPU fallback, warm timing, and max RSS.
- Software and CPU-SIMD rows are provenance-labelled parity oracles; they require
  exact checksum/parity, warm timing, and max RSS, not GPU identity.
- ProcessingIR recovery TODO 649/650 is separate evidence and cannot prove Web
  or Draw IR completion.

### R7–R9 audit status (2026-07-31)

- **R7: open.** CUDA has retained-session/pending-resource source contracts;
  Vulkan has the rect-list counter and batch boundary; Metal has the pending
  primitive boundary. None has the required current-host physical receipt with
  counters and warm latency/RSS for this Draw IR workload. Generated-compute
  wrappers are not a substitute for an Engine2D Draw IR submission receipt.
- **R8: open.** `RequireDeviceRegion` fails closed unless Vulkan returns
  `device_region`; the source contract and focused probe assert that policy.
  No live device-region receipt exists.
- **R9: blocked, not passed.** `build/r9-linux-vulkan/RESULT.md` records that
  the admitted pure-Simple stage2 compiler linked the focused probe with the
  generic `--runtime-bundle core-c-bootstrap` (no Rust seed), then returned
  `backend unavailable: vulkan` before submission. That does **not** prove this
  bundle supplies a physical Vulkan provider: `simple-runtime` compiles
  `rt_vulkan_*` stubs when its `vulkan` feature is absent. The canonical Linux
  host-GPU provider lane is instead the feature-built runtime at
  `build/simpleos_gpu_host/<arch>-vulkan-cuda-runtime-target/bootstrap`, built
  with `vulkan,cuda,runtime-symbol-table`; it is currently absent. Device
  inventory alone is not a receipt. Do not rerun the exhausted CUDA/Vulkan
  attempts until that provider is linked and the factory emits a concrete
  initialization diagnostic or a live receipt.

## Task Ownership

| Lane | Sidecar | Write scope | Merge gate |
|---|---|---|---|
| R1 lifecycle/cutover | small agent | `ui.browser`, browser session, focused specs | ownership/shutdown review |
| R2 events/metadata | small agent | interaction adapters and producer specs | ancestry/wheel behavior |
| R3 iframe | small agent | web paint/layout + iframe spec/manual | CPU parity before cutover |
| R4 text guards | small agent | hosted/Metal compatibility guards | highest-model font review |
| R5/R6 executor+allocations | disjoint small agents | executor and producer collections | behavior plus measurements |
| R7/R8 backend work | one agent per backend | backend-owned files only | physical-device receipt |

Merge owner: primary coordinator. Final reviewer: best available high-capability
model. Shared interfaces remain `DrawIrComposition`,
`engine2d_draw_ir_adv_composition`, `draw_text`, and `RenderBackend.submit_batch`;
sidecars must not invent parallel producer or font APIs.

## Done Gate

This plan is complete only when R1-R9 have executable evidence, generated/manual
system documentation is current, strict GPU requests have no silent CPU path,
and the Linux/macOS live matrix passes. Source contracts alone cannot close a
live rendering row.
