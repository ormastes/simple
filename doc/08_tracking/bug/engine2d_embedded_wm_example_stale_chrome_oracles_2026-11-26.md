# BUG: engine2d embedded-surface WM example asserts a chrome stream the product no longer emits

Status: OPEN (2026-11-26), split from
`engine2d_strict_vulkan_evidence_fails_after_shared_session_example_2026-08-19`
(whose named Vulkan mechanism is verified fixed on Linux aarch64).
Where: `test/02_integration/rendering/engine2d_embedded_surface_spec.spl`,
example "composites a canonical offset translucent WM window on shared Vulkan
and Metal sessions"; `src/lib/common/ui/window_scene_draw_ir.spl`.

## Measured (release/1.0.0 79445b063c4, Linux aarch64 GB10, seed cargo-target-wr-seed1126b)

`simple test test/02_integration/rendering/engine2d_embedded_surface_spec.spl`
-> 10 executed, 9 passed, 1 failed (this example). Dumped `window-win` stream:

```
win-shadow rect 5,6 120x80 0x28000000      <- commands[0] (oracle: body, alpha 0x33)
win-body rect 0,0 120x80 0xFFE8E8E8        <- commands[1] (oracle: 120x80 with 120x80 hit_rect; actual hit_rect 0x0)
win-titlebar ... win-close-label
content-win emb=14,68 112x44: win-content-invalid rect (fail-closed placeholder)
```

## Three independent causes

1. **Unthemed chrome stream.** No active WM theme snapshot is installed in the
   spec process (`active_wm_theme_snapshot_present()` false), so
   `window_scene_draw_ir.spl` emits the "historic" plain-RECT stream (shadow
   first, no hit/style rects); the index-based oracles do not match it. The
   themed branch was read from source, not dumped: it starts with the body box
   but puts a 120x28 titlebar at index 1, so it does not match the oracles
   either (they expect 120x80 at index 1). Owner decision: which stream the
   spec pins (installing e.g. `aetheric_dark_theme_render_snapshot()` via
   `apply_theme_render_snapshot_to_wm_chrome`, then resetting, or keeping the
   historic stream), with commands selected by `component_id`, not index.
2. **Stale content fixture.** The fixture frame is 120x52 at (10,64); the
   product content rect is `_shared_wm_scene_window_content_rect` =
   (x+4, y+32, w-8, h-36) = 112x44 at (14,68), the same rule the compositor
   enforces (`attach_window_pixel_content`). The size mismatch makes the
   scene draw the magenta invalid placeholder instead of the image.
3. **Shared Vulkan child alpha oracle.** `alpha_result.pixels[0]` reads
   `0x33FF0000`; oracle `0x33330000`. Probed: the strict Vulkan path turns the
   first rect into `eng.clear(color)` (`draw_ir_adv.spl`
   `_engine2d_draw_ir_execute_strict_vulkan_primitives`), and an explicit
   transparent clear followed by the same rect also gives `0x33FF0000` —
   correct straight-alpha src-over onto transparent. Shared offscreen layers
   are documented as straight-alpha words (`backend_vulkan.spl`), so
   `0x33330000` (premultiplied-looking) appears to be the stale side; confirm
   with the owner before rewriting. For comparison, the same batch on a 2x2
   CPU engine (`engine2d_draw_ir_adv_batch`, `cpu_mirror`) gives `0xFF330000`
   (composited onto the opaque black clear), and a second translucent rect on
   the same Vulkan child gives `0x5CFF0000` (straight-alpha accumulation).

The fresh-device composition in the same example already passes on device:
`readback_source=device_readback backend_handle=1 rendered=17 skipped=0`,
pixels byte-equal to the CPU oracle.
