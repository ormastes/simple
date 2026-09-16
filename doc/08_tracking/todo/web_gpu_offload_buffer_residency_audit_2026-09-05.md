# Web renderer GPU offload / buffer residency audit — open items

Date: 2026-09-05. Audit of the web render path
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`
-> `src/lib/gc_async_mut/gpu/engine2d/**`) for host/device boundary crossings
and buffer-location defects.

Two defects found in the same audit were FIXED and are not listed here (the
double ancestor walk in `content_paint_hidden_by_ancestor`, and the repeated
`+`-on-text gradient-stop accumulator). The already-recorded route-key defect
(`web_draw_ir_route_key_serializes_whole_scene_per_frame_2026-09-05.md`) is out
of scope here and is NOT restated.

Nothing below was measured with a timer: this host has no Vulkan/Metal device
available to this session, so every cost figure is a call/iteration count read
off the source, not a wall-clock measurement.

## 1. A whole Engine2D (and therefore every device buffer) is created and destroyed per route call

`simple_web_layout_engine2d_fast.spl:265-281`
(`_simple_web_layout_render_draw_ir_composition`) does
`Engine2D.create_with_backend_fast(...)` … `engine.shutdown()` for **every**
call, and the presenter's upload route
(`simple_web_html_engine2d_presenter.spl:455-462`) does the same with
`Engine2D.create_requested_backend(...)`. Per frame that is:

| phase | engine create/destroy pairs per frame |
|---|---|
| sampling (`state.complete == false`, first 3 frames per route key) | 4 — gpu route (1) + upload route's software oracle (1) + upload route's presenter engine (1), and the oracle engine again on the second ordering leg |
| steady, `should_offload == true` | 1 |
| steady, `should_offload == false` | 3 (software oracle + presenter engine, per frame) |

`VulkanBackend.init` / `MetalBackend.init` allocate the framebuffer, staging
and font buffers on every one of those inits, at an extent that has not
changed between frames — item 2(d) of the audit brief, at the coarsest
possible granularity. The warm pools that `backend_metal_font.spl`
(`packed_pool`, :215-232) and `backend_vulkan.spl` (`font_params_pool`,
:285-286) added are torn down with the engine each frame, so they can only ever
warm up *within* one frame.

Not fixed: an engine cache keyed on `(backend, width, height)` needs a real
device to prove it does not leak or reuse a poisoned context across frames, and
the lifetime contract (`_discard_pending`, `completion_unknown`) is device
state. This is the largest item in the audit and should be the next piece of
work on this path.

## 2. Full-surface per-pixel interpreted loops on every GPU-route frame

- `simple_web_layout_engine2d_fast.spl:379` `_web_draw_ir_pixel_fingerprint` —
  called at :504 on **every** steady-offload frame over the entire readback.
  One interpreted loop iteration per pixel: 480,000 at 800x600, 8,294,400 at
  3840x2160.
- `simple_web_layout_engine2d_fast.spl:369` `_web_draw_ir_pixels_equal` —
  same shape, on every steady non-offload frame (and twice per sampling frame,
  at :563-565).
- `engine2d/backend.spl:17-23` `engine2d_readback_with_identity` — sums every
  pixel to build `Engine2DReadback.checksum` at every readback construction,
  whether or not any caller reads the field.

Not fixed: the obvious substitution — compare `Engine2DReadback.checksum`
instead of hashing the pixels — is unsafe. That checksum is a plain modular
SUM (`backend.spl:21`), so it is order-independent and trivially collidable,
and the route code deliberately chose a collision-resistant identity (see the
comment at `_web_draw_ir_key`). Making this cheap needs a bulk `rt_*` hash over
the pixel block computed once at readback time and reused by both the
fingerprint and the equality check; that is a runtime addition, not a local
edit, and it cannot be validated against a device readback here.

## 3. Host staging buffers allocated and freed per text batch (Metal)

`backend_metal_font.spl:357` (`rt_alloc(packed_bytes)` / `rt_free` at :364) and
`:367` (`rt_alloc(4)` / `rt_free` at :379) allocate and free host memory on
every packed font dispatch, i.e. once per text batch per frame. The *device*
side of exactly this buffer is already pooled by `_packed_slot` (:214-224)
against a fixed `METAL_FONT_PACKED_MAX_BYTES` cap, so the host staging buffer
could be pooled the same way with the same cap and the 4-byte word buffer could
be a single long-lived allocation.

Not fixed: reaching `_draw_packed` requires a live `MetalSession` with a
compiled `pipe_font_atlas_composite_packed`, so no spec on this host can prove
the change is behaviour-preserving. Cost is 2 host malloc/free pairs per text
batch — real but small next to items 1 and 2.

## 4. `gpu_lut_pack_dense` writes one FFI call per palette entry

`engine2d/backend_metal_runtime_ops.spl:68-71` loops `rt_ptr_write_i32` once
per palette entry while the bulk helper `rt_write_u32s_to_raw`
(`metal_write_u32s_to_ptr`, :28-30) exists. The comment at :40-46 says this is
deliberate for the upload-only LUT pilot. Recorded for completeness only:
palettes are ≤256 entries and this is not on the web render path. No action
proposed.

## 5. Linear scan of the image list inside the per-node paint loop

`simple_web_html_layout_renderer_paint_layout.spl:2185`
`_html_draw_ir_image_index` scans `images` linearly and is called at :2263,
:2403 and :3098 — the last of those inside the per-node × per-background-layer
loop of `_html_draw_ir_commands`. Cost is O(nodes × layers × images) per frame.

Not fixed: replacing it with a URI→index dict built once per frame is
straightforward but changes a signature used by three call sites plus the
background-layer lowering, and `images` is typically single-digit in every
existing fixture, so the win could not be demonstrated by any spec available
here. Worth doing when an image-heavy fixture exists to measure against.

## 6. `build_ancestor_clip_cache` is built twice per frame

`simple_web_html_layout_renderer_paint_layout.spl:2755`
(`_html_draw_ir_visible_nodes`) and `:2825` (`_html_draw_ir_commands`) each
build the cache, and `simple_web_html_layout_renderer.spl:1478,1481` calls both
back to back with identical arguments. One redundant O(node_count) pass per
frame (it short-circuits to empty when no node declares an overflow clip).

Not fixed: threading the cache through changes the signature of both private
functions and a third call site at `simple_web_html_layout_renderer.spl:2435`
that calls `_html_draw_ir_visible_nodes` alone — more churn than the one linear
pass is worth without a measurement to justify it.

## 7. The steady non-offload route round-trips the device purely to verify

`simple_web_layout_engine2d_fast.spl:539-548`: when `should_offload` is false
the route still renders the software oracle, uploads it to the device, reads
the full surface back, compares it pixel-for-pixel, and then returns pixels
that are equal to the oracle either way. The device work is pure verification
and the readback is full-surface where the brief's item 2(c) would want a
changed-region readback.

Not fixed: this is the designed policy (an honest A/B that keeps proving the
device still agrees), not an oversight, and changing it is a policy decision
rather than a defect fix. Recorded so the cost is visible: one full upload plus
one full readback per frame on the non-offload steady state.

## Completion ledger — opened 2026-09-05

Which of the items above can actually be finished on this machine, and which
are blocked on hardware that does not exist here. "Completable" means the fix
is pure Simple and its effect is provable by a spec without a GPU device; it
does NOT mean the speedup can be measured here, and no item below may ship
with a measured claim attached.

| # | Item | Status | Why |
|---|---|---|---|
| 1 | Per-route Engine2D create/destroy | COMPLETABLE | Engine lifetime is pure Simple; a reuse cache is provable by counting creates in a spec |
| 2 | Full-surface per-pixel loops + collidable checksum | COMPLETABLE | The checksum being a plain modular SUM is a correctness bug, not just a cost; provable directly |
| 3 | Metal host staging alloc/free per text batch | COMPLETABLE | Introduced by the packed-font change in this same PR; pooled the same way the device buffers are |
| 4 | `gpu_lut_pack_dense` per-entry FFI | COMPLETABLE | A bulk helper already exists and is already used elsewhere in the same file |
| 5 | Image-list linear scan in the per-node loop | COMPLETABLE | Pure indexing change |
| 6 | `build_ancestor_clip_cache` built twice | COMPLETABLE | Pure dedupe |
| 7 | Verification-only device round trip on the steady non-offload route | COMPLETABLE | Route logic is pure Simple |
| — | DirectX GPU text path | BLOCKED | No Windows and no DXVK host; see the DirectX gap record |
| — | Device measurement of the Metal packed path | BLOCKED | No Metal-featured binary on this host |
| — | Web route key whole-scene serialize + hash per frame | BLOCKED-BY-DESIGN | Needs a generation counter on `DrawIrComposition`, a wide struct change across every DrawIR producer |
| — | Simple side of the Chrome comparison | OUT OF SCOPE HERE | The renderer is not linked into `simple_runner.spl`; that is a harness build change, not a perf fix |

**Rule for anyone closing one of these:** every fix needs one runnable check in
the nearest existing spec, and the spec must be run and its verdict line
quoted. A source-only argument that a loop got shorter is not evidence. None of
these may be reported as a speedup, because nothing here can measure one.

## Items 1 and 7 closed 2026-09-05

**Item 1 — engine reuse.** Both route paths now acquire and release a pooled
engine instead of creating and destroying one per call:
`simple_web_layout_engine2d_fast.spl` (slot cache plus drain and counters) and
`simple_web_html_engine2d_presenter.spl`. The key is the canonical backend name
plus the extent. Invalidation is fail-closed and re-evaluated on BOTH park and
acquire: extent change, backend change, a `selected_backend_name` that does not
match the canonical request (so a silent CPU fallback is never parked as though
the device came up), an uninitialized Vulkan or Metal backend,
`completion_unknown`, and an unknown Vulkan font state. Anything not parked is
shut down.

Measured over 4 frames at 8x4 on the "vulkan" route: fast-engine creates went
2, 0, 1, 0, and the presenter attempted 1 create across all four frames where
it previously did one per frame. One discard in that window was a genuine
`completion_unknown` catch, which is the fail-closed path working rather than
churn. Note `web_draw_ir_gpu_route_sample` has no production caller, so the
production benefit is the execution render and the presenter.

**Consequence to be explicit about: parked engines are process-lifetime
resident.** Both caches expose a drain (`web_draw_ir_engine_cache_drain`,
`web_presenter_engine_cache_drain`, the first reachable through
`web_draw_ir_gpu_route_policy_reset`), and **no production caller invokes
either** — only specs do. So up to 4 parked engines per cache, each holding a
framebuffer, staging buffer and font atlas, stay alive for the life of the
process. At 4K that is not a rounding error.

This is a deliberate trade, not an oversight, and the peak footprint is not
worse than before: the same buffers previously existed during every frame and
were freed after. What changed is that they are now held between frames instead
of reallocated. The open work is wiring a drain into a host shutdown or
surface-teardown path so a long-running host can release them; until that
exists, treat the residency as the known cost of this item.

**Item 7 — removed as waste.** In the steady non-offload branch both outcomes
published the CACHED evidence, `pixels_match` was never updated, no receipt was
written, and the returned pixels equalled the oracle either way, so nothing
could observe the comparison. It is now an oracle-only route. Sampling frames
still run the full A/B, so the evidence that decides the route is unchanged.

Verified: `web_draw_ir_engine_reuse_spec` 7/7 (new: same-dims reuse, extent
change, backend change, failed engine not cached, drain teardown, presenter
invalidation, item 7), `web_gpu_present_paint_coverage_spec` 23/23,
`web_draw_ir_route_key_memory_spec` 1/1.
`simple_web_engine2d_renderer_spec` fails 7 both with the cache active and with
it force-bypassed, byte-identical, so that red is pre-existing and unrelated.

### Unconfirmed observation — do NOT cite this as a known defect

While item 1 was being written, a print inside the `Ok(engine)` arm of a
`val x = match <Result>:` appeared to fire twice for one call, and was first
written up as a live compiler defect that would have meant `engine.shutdown()`
ran twice per present. **It did not reproduce.** Two minimal cases on the same
2026-09-05 seed — a plain `Result<i64, text>`, and a class-valued
`Result<Eng, text>` whose arm calls a method — each executed the arm exactly
once. **The cause of what was observed has NOT been established** — only that
the stated defect does not reproduce in isolation. Do not substitute a
confident alternative explanation either; that would repeat the same mistake
one level up.

No bug record was filed, because filing an unreproducible compiler defect is
worse than filing nothing: it becomes a cited excuse for workarounds. The park
still sits outside the match, which is the right shape regardless. If anyone
sees this again, capture the FULL call path, not just the arm.
