# Web renderer: two full-surface readbacks per frame — NOT the presenter (2026-09-12)

Status: root cause located, **fix handed off** (device-side glass on the Vulkan
backend). The measurement that locates it landed with this record.

## What was reported

`doc/10_metrics/ui/web_4k_showcase_gpu_boundary_audit_macos_2026-09-12.md`
ranked two boundary defects at the presenter:

* #2 "two full-surface readbacks/frame" at
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl:436`
  (damage blit) and `:598` (full surface);
* #4 "the presenter uses the GPU as a pass-through" at `:593-598` — the page
  host-painted, uploaded via `draw_image(0,0,w,h,pixels)` and read straight
  back, accounting for ~126 s of the 4K frame.

## What is actually true (measured, not inferred)

**Neither presenter site runs on the audited lane.** Presenter-owned counters
were added (below) and drained per frame by the audit driver. On the gate's own
configuration — `overview.html`, 900x760, `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native SIMPLE_VK_IMAGE_UPLOAD=u32 SIMPLE_VK_RECT_UPLOAD=u32`,
interpreter — both audited frames report:

```
[web-route-stage] readbacks_gpu_paint=0 readbacks_upload=0 host_paint_pixels=0
host_paint_pixels=0
presenter_readbacks_gpu_paint=0
presenter_readbacks_upload=0
readbacks_per_frame=2          <- unchanged, so the 2 are elsewhere
```

Why the presenter is not on this path: the audit drives
`simple_web_render_html_to_pixels_with_engine2d_backend` ->
`simple_web_engine2d_render_html_pixels` (`simple_web_engine2d_renderer.spl:1136`),
which at `:1143-1144` routes any page containing `<p>/<h1>/<button>/...` — every
real catalog page — into `simple_web_layout_render_html_pixels_engine2d`
(`simple_web_layout_engine2d_fast.spl:1260`). That entry consults the Draw IR
A/B route chooser only when `web_gpu_paint_enabled()`, i.e. only under
`SIMPLE_WEB_GPU_PAINT=1`, which the gate does not set. The default lane executes
the composition once and never reaches the presenter at all.

**The two readbacks are one device render each, both full-surface.** Per frame
the Vulkan order trace shows exactly two `readback-entry` lines, and
`vulkan_stat_note_readback` (`backend_vulkan.spl:2166`) is called once per
`read_pixels_with_source()`, so `readbacks=2 readback_pixels=1368000`
(2 x 684000) is two genuine whole-surface reads, not a double count. Their
positions in the trace identify them:

1. **The parent-material (glass) seed** —
   `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2583` calls
   `_engine2d_read_pixels_region` (`:2447`), whose documented D9 implementation
   reads the **whole** framebuffer and crops on the host because "no backend
   below exposes a device-side region read". The cropped seed is then
   `draw_image`-uploaded into an offscreen delta surface (`:2600`), rendered,
   read back and composited. The trace signature is
   `image-composite w=888 h=384 mode=1` -> `readback-entry` ->
   `image-composite mode=0`, and 888x384 = 340,992 = the
   `image_composite_stats max_px` the gate already prints. This is the real
   device -> host -> device pass-through on this lane.
2. **The final frame read** — the one timed call (`VK_T_READBACK`, bucket
   `readback n=1`), which the caller needs because the audited entry returns
   pixels.

So defect #4's shape (GPU used as a pass-through) is real and defect #2's count
is real; the FILE and the mechanism named in the metrics doc are not.

## Why this could not be fixed here, and who owns it

Cutting the count to <=1 requires the glass/backdrop composite to sample the
parent **on the device** instead of seeding an offscreen surface from a host
copy. Metal already has that path (`metal_device_glass_material_count`,
`draw_ir_adv.spl:2565-2573`); Vulkan does not, so the Vulkan lane falls into the
host-seed branch. The device-side region read / device glass belongs to
`backend_vulkan*.spl`, which is F30's file in this split and is explicitly out of
scope for this lane.

A narrower improvement is available in `draw_ir_adv.spl` without touching the
backend: route the seed through a Vulkan region read when one exists. That
reduces `readback_bytes` (5.47 MB -> ~4.1 MB at 900x760; 66.4 MB -> ~50 MB at
4K) but **not** `readbacks_per_frame`, so it does not satisfy the invariant on
its own. Recorded here rather than half-done.

## What landed

* `simple_web_html_engine2d_presenter.spl` — route-stage counters
  (`web_route_stage_note_host_paint`, `web_route_stage_drain`,
  `web_route_stage_host_paint_pixels`, `web_route_stage_readbacks`). Both
  presenter readback sites and every host-painted pixel handed to a device are
  counted. They are counted unconditionally; only emission is up to the caller,
  because a counter armed by an env var reads 0 exactly when it matters.
* `simple_web_html_engine2d_presenter.spl:638-650` — the upload-bound present on
  a non-CPU backend now records a reason
  (`[web-gpu-paint-decision] ... upload-bound:host-painted:...`), in the same
  shape the gpu-first lane uses for its declines. It is still a legitimate
  fallback; it is no longer a silent one.
* `src/app/ui/chrome_showcase/gpu_boundary_audit.spl` — drains the counters with
  the census (so both are per-frame), emits `host_paint_pixels`,
  `presenter_readbacks_gpu_paint`, `presenter_readbacks_upload`, and FAILs when
  `host_paint_pixels > 0`. An absent `[web-route-stage]` line reports
  `unavailable`, never 0.
* Selftest 6 -> 10 fixtures, all fatal. The new ones are a host-paint frame that
  must FAIL (byte-identical to the clean fixture except the route-stage line, so
  it is also the sabotage proof for this key), a route-stage frame with a
  measured 0 that must PASS, and two key-level assertions pinning
  `host_paint_pixels=0` vs `=unavailable`.

## Evidence

Gate: `scripts/check/check-web-vulkan-gpu-boundary-audit.shs`, page
`examples/06_io/ui/web_catalog/overview.html`, 900x760, 2 frames, interpreter,
lane flags as above. Verdict before and after this change is the same and is
honest about it:

```
FAIL — 2 frame(s) audited, violated: host_pixel_iterations=16 (>0):
font_atlas_pack_u32_to_u8:16; readbacks_per_frame=2 (>1); submits_per_frame=17 (>1)
```

`host_pixel_iterations` is F24's font atlas repack and `submits_per_frame` is
F30's; neither is claimed here. Frame times: 65,190 ms cold / 34,758 ms steady
on a host running a peer's GPU job concurrently — **ms are not comparable with
the metrics doc's 126,293 / 102,287**, the counts are.

Selftest: `PASS — selftest only, 10 examples, 0 failures`.

**Binary identity.** `build/cargo-r2/release/simple` = `39178424 1789197971`
cannot run this lane at all: it dies with `semantic: unknown extern function:
rt_vulkan_copy_to_buffer_u32`, a symbol registered in source at `17aec7247b6`
(2026-09-11) — that binary predates it, with or without the `u32` upload flags.
Every measurement above therefore used
`/private/tmp/claude-501/-Users-ormastes-simple/3a71a95b-c0a0-43b7-9597-7fd40e488d92/scratchpad/cargo-r2/release/simple`
= `37568056 1789199216`, bracketed identical before and after each run by the
gate itself.

## Not done, deliberately

* **4K (3840x2160) was not re-measured.** Every number here is 900x760. The
  metrics doc's ~126 s of 4K host paint was attributed to the presenter; the
  presenter counter reads 0 at 900x760, and the same claim at 4K has not been
  re-tested.
* **"A present-only frame performs 0 readbacks" is not exercisable** on this
  lane: the audited entry returns pixels, so it needs >=1 by construction, and
  no present-only entry that returns no pixels is reachable from it
  (`draw_ir_adv.spl:158` has a `no_readback` flag but no caller on this path).
  Pinning a trivial 0 would have been a spec that proves nothing.
* **The measured-mode (`SIMPLE_WEB_GPU_PAINT=1`) A/B samplers still run two
  device legs and a full host raster per sampling frame** — `fast.spl`'s
  `_web_draw_ir_choose_route` (sampling branch) and the presenter's
  `_sample_web_gpu_paint_choice` have the identical shape. An "oracle + upload
  leg once per key" fix was written and reverted from this change: it is off the
  default lane, the gate cannot observe it, and the file has five recent peer
  commits. Follow-up, not a silent carry.
