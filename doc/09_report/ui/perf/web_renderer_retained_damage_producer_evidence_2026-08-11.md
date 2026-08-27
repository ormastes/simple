# WebRenderer retained damage producer evidence — 2026-08-11

Status: PRODUCER VERIFIED; EXACT VULKAN FRAME SWITCH VERIFIED; LOCAL CONSUMPTION IMPLEMENTED, VERIFICATION FAILING.

`SimpleWebRenderSession` now publishes conservative frame-local damage metadata
without changing `DrawIrComposition` or introducing WebIR:

- first render and structural/style/resource/scroll/animation changes: FULL;
- exact retained composition reuse: NONE;
- text-input overlay/caret-only change with retained hit geometry: LOCAL over
  the clipped old/new input rectangles;
- missing overlay geometry: fail-open FULL.

The focused spec is
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session_damage_spec.spl`.
Three verification cycles were consumed: initial compact assignment syntax
failed parsing, the corrected run hit the 60-second CPU guard, and the final
run identified `pass` as a reserved keyword. Both source defects are corrected,
but the mandatory three-cycle cap forbids another run in this session.

The hosted production path already owns one persistent
`Engine2dCompositorBackend`; it does not recreate Engine2D per frame. Exact
producer-revision reuse was previously disabled on Vulkan because cache
admission accepted `device_readback` but rejected the backend's completed
`host_cache_after_device_copy` receipt. Admission now accepts either only
when both backend handle and device identity are nonzero.

The retained receipt records `present_mode=host_cache` and
`device_present=false`: this is a completed device-to-host cache copy, not a
swapchain present or display scanout. Focused receipt coverage passes 4/4,
including zero submission/readback work on exact reuse.

Pinned-llvpipe compositor revision-cache spec: **3 examples, 0 failures**. The
live Vulkan case renders once, receives a completed host-cache/device identity,
then submits the identical producer generation/revision/composition and proves
`revision_render_count=1`, `revision_reuse_count=1`, and identical pixels. This
is a real zero-raster exact frame switch, not a reconstructed screenshot.

Changed-revision LOCAL consumption is implemented in the persistent
`Engine2dCompositorBackend`. Compatible stable-resource revisions use the
shared composition classifier, replay through the DrawIR damage executor, and
request a damage-plan present. NONE retains the existing zero-work path and
incompatible or uncertain changes fail open to FULL.

The focused compositor spec now includes a 4x4 Vulkan case whose intended
receipt is one exact 1x1 rectangle (4 transferred bytes), followed by complete
pixel parity against a fresh software replay. Its final bounded run passed the
three existing examples but failed this new example (3/4) with the runner's
generic truth assertion and no failing step location. Three verification/fix
cycles were consumed, so the repository iteration guard requires escalation
instead of another retry. Consequently the LOCAL consumer and its byte/parity
claim are **not verified**.

No 8K/80 claim is made by this change.

## Retained tiled DrawIR preparation

The Web GPU/CPU tile adapter now exposes `TileLanePlan`. A plan owns the exact
counting-sort bins, live viewport mask, ragged tile geometry, and command
geometry/parent-sampling proof columns. Repeated frames with unchanged
geometry reuse those arrays directly; paint-only changes still replay the new
commands. Moved geometry or a changed parent-sampling classification fails
closed as `stale-tile-lane-plan` before clear, raster, submission, or readback.

The plan builder bins `DrawIrCommand` rectangles directly and no longer builds
a temporary `TileOp` object list. Focused evidence passes 2/2: one retained
plan produces the correct changed pixel across two paint-only frames, while a
moved command is rejected with zero raster. This proves the reusable producer
mechanism, not 8K latency or Vulkan presentation throughput.

## 8K exact frame-switch attempt

`test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl` exercises the
real persistent compositor revision cache at 7680x4320. The seed frame is
excluded from timed reuse; the row requires one render, exact reuse counters,
complete checksum, p50/p95, RSS, fallback, and readback mode.

Interpreter runs with 200 and 5 reuse frames both exceeded the 180-second
watchdog before producing a row. A self-hosted aggressive native entry-closure
build then also exceeded 180 seconds without a source diagnostic. The three
allowed cycles are exhausted, so exact 8K frame switching remains unverified.
The concrete build/runtime isolation and possible 132.7 MB result-copy issue
are tracked in
`doc/08_tracking/bug/web_draw_ir_8k_frame_switch_native_build_timeout_2026-08-11.md`.

The frame-switch API has since been split from pixel readback. Exact hits use
`try_reuse_draw_ir_composition_revision`, which returns only a scalar retained
surface receipt and records zero raster, submission, and readback work. It
never unwraps or returns the cached 8K pixel payload. Focused exact/miss/content
sabotage coverage passes 3/3. The benchmark is updated to time this receipt,
but no new 8K pass is claimed.

The bounded JIT evidence runner now captures full diagnostics under `build/`
and admits exactly one `status=pass` row. Its first run found a native-runtime
closure defect before rendering: the deployed self-hosted binary does not
export `rt_struct_receiver_valid`, so Cranelift rejected the compositor methods
and fell back to the interpreter; that fallback then exceeded the 180-second
guard without a row. Source and runtime declarations already exist, but the
deployed binary is stale. This remains a compiler/runtime deployment blocker,
not an 8K receipt-performance result.

The hosted browser registry now consumes this receipt before calling the
pixel-bearing raster API. On a hit it retains the already-published WM content
surface, updates only address metadata, increments an explicit frame-switch
counter, and publishes no duplicate `WmContentFrame` after the prior frame was
consumed. A still-pending prior frame remains available. Misses fall through to
the unchanged LOCAL/FULL raster path.

Evidence: backend receipt behavior passes 3/3; production call-order/no-
duplicate-frame contract passes 1/1. This proves the zero-pixel-return path is
wired, not its 8K latency. The native 200-frame row remains required.

The publication decision is now a clean hosted helper independent of the
renderer-process dependency closure. Semantic evidence passes 1/1: after one
seed render, an exact consumed frame selects `none`, an exact still-pending
frame selects `frame`, and a changed revision selects `raster`. Both exact hits
carry zero raster/readback counts; the backend render count remains one. The
registry source/order contract also passes 1/1. This replaces the earlier
source-only consumer claim with executable decision evidence.

## Exact composition-patch damage follow-up

Stable-resource frames with unchanged batch source/embedding metadata now
derive damage from `draw_ir_patch_between`. The session applies the patch and
requires full-command round-trip equality before publishing LOCAL rectangles.
Patch bounds are clipped to the viewport and exact duplicates are removed.

The path fails open to FULL for viewport/resource changes, incompatible batch
metadata, failed round trip, or changed commands without usable bounds. An
empty proven patch publishes NONE. The earlier input-overlay exact rectangle
path remains the first specialized case.

The decision logic is now owned by the backend-independent
`common.ui.render_opt.composition_damage` module rather than duplicated in the
Web session. Its focused spec covers exact NONE, clipped LOCAL style damage,
old+new LOCAL move bounds, and fail-open FULL behavior. The self-hosted focused
run passed 4/4 examples on 2026-08-11.

The earlier `bin/simple check` of the complete browser render-session module
exceeded the 180-second watchdog while compiling its large dependency closure
and did not report a source diagnostic. The shared classifier is VERIFIED;
the browser integration remains IMPLEMENTED BUT NOT EXECUTED end-to-end. No
runtime or 8K throughput claim is made.

## 8K retained-result payload removal

The hosted compositor now separates retained-surface validity from the
optional pixel-bearing `Engine2dDrawIrAdvResult`. At or below 1920x1080 the
legacy result-returning cache remains available. Above that cap—including 4K
and 8K—the persistent Engine2D surface, composition/resources, checksum,
backend identity, and readback/present provenance remain retained, while the
second full pixel result is released. Exact hosted frame switches still return
the scalar zero-raster/zero-submit/zero-readback receipt, and LOCAL composition
damage continues from the retained surface.

The focused structural contract passes 2/2. At 7680x4320 this removes one
explicit 33,177,600-pixel retained result reference (132,710,400 ARGB32 bytes,
excluding boxed/runtime overhead). This is a data-lifetime optimization, not
measured RSS proof; no 8K/80 admission is claimed.
