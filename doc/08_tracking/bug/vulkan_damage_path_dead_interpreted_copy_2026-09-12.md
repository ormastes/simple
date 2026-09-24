# The Vulkan damage path was dead, and was itself an interpreted per-pixel copy (2026-09-12)

Status: FIXED on the native readback lane (steady partial frame 7 ms -> 2 ms at
900x760, 19 ms -> 6 ms at 1080p); **deliberately NOT fixed on the default lane**,
for a reason stated below rather than papered over.
Platform: macOS 25.5.0 / Apple M4, `SIMPLE_EXECUTION_MODE=interpreter`, backend `vulkan`.
Follows: `vulkan_readback_interpreted_unpack_dominates_frame_2026-09-12.md` (F8).
Spec: `test/02_integration/gpu/engine2d_vulkan_damage_scoped_mirror_spec.spl` (6/6).

Binaries, `stat -f '%z %m'` identical before and after every run:
`build/cargo-r2/release/simple` = `39368072 1789171430` (newer than the profile
doc's `39405288 1789115380`; it carries F8's interpreter externs).
`bin/release/aarch64-apple-darwin-macho/simple` = Sep 7 16:38, 26264696 bytes.

## Symptom

F8 measured `damage_valid=false mirror_valid=false` on every frame:
`_refresh_host_damage` never executed, so every dirty readback re-downloaded and
re-unpacked the whole surface. Routing to it would not have helped, because its
scatter is a nested interpreted `while row / while col` element copy — the same
684k-iteration class it was supposed to avoid.

Root cause of the deadness: **nothing ever produced a damage plan.**
`stage_present_damage` is the only writer of `present_damage_rects`, and it is an
external API no caller in the web/Draw-IR lane invokes. The backend's own draw
calls recorded no footprint at all.

## Fix

- **Draw calls accumulate their own damage union.** A draw publishes its
  destination rect with `hint_damage(x, y, w, h)` immediately before it
  dispatches; `_dispatch_framebuffer_checked` — the single funnel every
  framebuffer dispatch passes through — consumes it in `consume_damage_hint()`
  and folds it into a per-frame `(x0,y0,x1,y1)` union. Hints are attached at
  `clear`, `draw_rect`, `draw_rect_filled`, the axis-aligned-line rect arm,
  `draw_gradient_rect`, and the image composite (which bypasses the funnel but
  knows its rect exactly).
- **Fail-safe by construction.** An absent hint means "this primitive's
  footprint is unknown" and marks the WHOLE surface damaged, so forgetting a
  hint costs speed, never correctness. The rect-batch enqueue paths (which
  bypass the funnel) and the uninitialized-text CPU-raster arms mark full
  explicitly; so does a dispatch that FAILED, since a failed dispatch leaves the
  device in a state the hinted rect no longer bounds. An active clip can only
  shrink the painted area, so ignoring it keeps the union a superset.
- **The dirty readback consumes it** (`read_pixels_with_source`, not `present`).
  This is the load-bearing placement: after F8's dedup the page path reads
  pixels BEFORE present and then hits the `host_mirror_frame_fresh` early
  return, so `present()` never reaches a refresh branch at all. The one
  remaining full download per frame lives in the readback's dirty arm, and that
  is where damage has to be consumed to pay off.
- **`_refresh_host_frame_damage`** re-downloads only the union, **one native
  call per damaged row** (`vulkan_sffi_readback_u32_alloc`, F8's
  scalars-in / array-out primitive — the only shape this lane marshals). It
  declines (returning false, caller falls back to the full refresh) when the
  mirror is invalid, the damage is full, the row count exceeds 16384, or the
  union covers half the surface or more, where one contiguous download is
  cheaper. The whole-surface checksum is refreshed with one native fold, so the
  mirror identity stays honest without a second unpack.

### What is NOT claimed: zero interpreted iterations

The byte->u32 **unpack** is now native. The **scatter** into `host_buf` is still
one interpreted element write per damaged pixel, and there is no way around that
on this lane: every extern that takes a destination array is refused on the
interpreter path (F8 established this — `vulkan_sffi_copy_u32_into` is `"vvi"`
and falls back to its own element loop). So `mirror_copy_iterations` equals
`damage_rect_px` by design; the win is that it is bounded by the DAMAGE instead
of the surface (100 instead of 684,000 for a 10x10 rect). Reporting it as 0
would have been a lie.

### Why the default lane is unchanged

`vulkan_sffi_readback_u32_alloc` returns `[]` without
`SIMPLE_VK_READBACK=native`, so the damage route declines and the full refresh
runs. Every alternative on that lane — a per-row download through
`vulkan_sffi_readback_u32_into`, or a checksum recomputation — is itself an
interpreted per-pixel loop, so a damage-scoped default path would move the
iterations rather than remove them, which is exactly the trap F8 named. The
default lane is fixed by deploying a seed carrying F8's symbols, not here.

## Measured, 8-frame probe, frame 0 = full clear, frames 1-7 = one 10x10 rect

`build/perf/f9/probe_partial.spl`, `SIMPLE_TIMEOUT_SECONDS=0`, one at a time.

| lane | size | frame 0 (full) | steady (median f4-f7) | damage_rect_px | mirror_copy_iterations |
|---|---|---|---|---|---|
| native, after | 900x760 | 7 ms | **2 ms** | 100 | 100 |
| native, after | 1920x1080 | 19 ms | **6 ms** | 100 | 100 |
| native, sabotaged (damage forced full) | 900x760 | 7 ms | 4-6 ms | 684000 | 0 |
| default (`cargo-r2`) | 900x760 | 2445 ms | 2450 ms | 684000 | 0 |
| default (deployed Sep-7 binary) | 900x760 | 7181 ms | 7217 ms | 684000 | 0 |

Sabotage check, run against the SPEC (not merely inferred from the probe):
forcing `consume_damage_hint` to always widen to full gives
`6 examples, 2 failures` — the reproduce and two-rect examples go red on the
counters — and turns the probe's counters into
`damage_rect_px=684000, mirror_copy_iterations=0` with the steady frame back to
4-6 ms. Reverted; 6/6 green again.

Two defects found in review of the first cut of this change and fixed before
landing, each with a spec example:

- **The damage arm cleared `dirty`.** That sent `present()` down its `not dirty`
  noop arm, whose receipt reports `frame_present_mode="none"` and leaves
  `readback_completed` / `host_cache_refresh_completed` FALSE on a frame that
  really did read back. F8's arm deliberately does not clear `dirty`; the damage
  arm now matches it, so both routes produce the same receipt.
- **The dedup arm reported a nominal transfer.** It overwrote
  `present_readback_bytes` with the full `w*h*4` even when the readback moved
  only a rect. The readback now carries its real transfer forward
  (`readback_frame_bytes` / `readback_frame_rects`).

**In-place patching does NOT write through a handed-out readback** — measured,
not assumed. This is the first path that writes into `host_buf` rather than
rebinding a fresh array, so it is the first that could have disturbed pixels an
earlier readback already handed out (the hazard F8's spec pins but whose
examples never reach this route). A spec example holds a frame-1 readback across
a frame-2 damage patch and confirms it is unchanged. There is no native
array-clone extern on this lane, so had it written through, the only repair
would have been to pay back a full-surface copy.

Regression: F8's `engine2d_vulkan_readback_unpack_cost_spec.spl` stays 6/6, and
`backend_vulkan_drawing_spec.spl` stays at its pre-existing 40/44 (identical
before and after, as F8 recorded).

## The page path's "unreconciled 1.44x" is gone (not attributed)

Re-measured on the page entry `simple_web_layout_render_html_pixels_engine2d_at_time`
(`build/perf/f9/probe_page.spl`, fixture `examples/06_io/ui/sample_web_renderer_sanity.html`):

| lane | 900x760 steady | 1920x1080 steady |
|---|---|---|
| default (`cargo-r2`) | 2453 ms | 7397 ms |
| `SIMPLE_VK_READBACK=native` | **18 ms** | **28 ms** |

Default lane, same probe: 2453 ms @900x760 and 7397 ms @1080p — each almost
exactly ONE 684k / 2.07M interpreted unpack. The 2026-09-11 page probe measured
7.2 s @900x760 against the fixture probe's 5.0 s, and that gap is **gone, but
not attributed**: the profile's own counters showed exactly 2 unpack calls per
frame and explicitly ruled out a third, so calling the removed term "another
unpack" would overclaim. What is certain is that it was pixel-linear and that
F8's present dedup removed it.

At 18 ms / 28 ms on the native lane the page path is no longer pixel-dominated,
so the profile's three remaining candidates (the `draw_image` blit in
`simple_web_html_engine2d_presenter.spl`, the degraded-retry second layout pass,
a deep `[u32]` copy across the browser_renderer boundary) are not the
explanation and need no fix. **What dominates the residual 18 ms is the
per-frame document pipeline** — profile row #9,
`_simple_web_layout_compose_document` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
~10 ms/frame, re-running parse/style/layout/Draw-IR on an unchanged document.
That file is owned by another agent this session and is not touched here; it is
a (document, viewport) caching problem, not a per-pixel loop.

This frame is dominated by a full-surface clear, so it takes the full-refresh
route by design; the damage work above pays off on partial-update frames, not
on this fixture.

## Coverage limits, stated rather than implied

- **Unhinted primitives always take the full route:** circle, circle-filled,
  triangle, ellipse, arc, non-axis-aligned or thick lines, the rect-batch
  enqueue paths, and CPU-raster text. They are not wrong, just not accelerated;
  each is one `hint_damage` call away whenever a lane needs it.
- **`stage_present_damage` -> `present` -> `_refresh_host_damage`**, the original
  externally-planned damage route, now downloads through the SAME native per-row
  primitive (falling back to `vulkan_sffi_read_buffer_regions_bytes` +
  `_bytes_to_pixel_array` only where the native arm is absent) and reports the
  same two counters. Its scatter remains interpreted for the reason given above.

## The two "dormant 684k loops" — reachability checked, no change made

F8 filed `_web_draw_ir_pixel_fingerprint` and `_web_draw_ir_pixels_equal`
(`simple_web_layout_engine2d_fast.spl`) as follow-ups. Grep + counter evidence:

- **`_web_draw_ir_pixel_fingerprint` is not on any frame path.** Its only caller
  is the `pub web_draw_ir_oracle_fingerprint` diagnostic seam (`:675`), whose
  only consumers are `web_draw_ir_engine_reuse_spec.spl:218-239` — a spec that
  exists to show the fingerprint DISCRIMINATES, and which at `:211` asserts
  `web_draw_ir_fingerprint_pixels_scanned() == 0` on a steady frame. Deleting it
  would delete a live spec's subject. Left alone.
- **`_web_draw_ir_pixels_equal` is reachable, twice, on the AUTHORIZATION path
  only** (`:946` steady re-anchor, `:1046-1047` validation), never per steady
  frame. At `:946` a device-checksum comparison already short-circuits it
  whenever both checksums are present. At `:1046-1047` the exact compare IS the
  proof — the file states explicitly why the order-independent checksum is not a
  parity proof — so replacing it with a checksum would weaken authorization, and
  a checksum pre-filter buys nothing because computing the oracle's checksum is
  the same 684k loop. Left alone, deliberately, rather than restructured.

Neither is a steady-frame cost. F8's "~2.4 s/frame when the route authorizer
runs" is right about magnitude and about frequency: per validation, not per frame.

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TVraTPgGDVypESTsVqXPgi
