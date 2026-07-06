# Engine2D Draw-IR `<img>` / background-image path has no resolver

- **ID:** engine2d-draw-ir-image-path-no-resolver-2026-07-06
- **Status:** Open
- **Area:** ui / gpu / engine2d / browser_engine
- **Date:** 2026-07-06

## Summary

The Engine2D advanced Draw-IR executor
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`) can render
`DRAW_IR_COMMAND_IMAGE` commands, but only when the caller supplies a matching
resolved bitmap through the `images: [Engine2dResolvedDrawIrImage]` list
(`engine2d_draw_ir_adv_batch_with_images` /
`engine2d_draw_ir_adv_composition_with_images`). The HTML layout renderer path
never populates that list, so no `<img>` or CSS `background-image` bitmap ever
reaches the executor.

## Why the image op is not emitted from HTML today

- The HTML layout renderer (`simple_web_html_layout_renderer.spl`) emits a
  `DRAW_IR_COMMAND_RECT` for every box. It does **not** emit
  `DRAW_IR_COMMAND_IMAGE` for `<img>` elements or for `background-image: url(...)`.
- The `HNode` captured by layout does not carry the resolved `src` / URL bytes,
  and nothing decodes the referenced resource into an
  `Engine2dResolvedDrawIrImage` to hand to the executor.
- Consequently, emitting `DRAW_IR_COMMAND_IMAGE` from the HTML path right now
  would **regress** `<img>` rendering: the executor would find no resolved image
  for the URI, increment `skipped_command_count`, and paint nothing — worse than
  today's placeholder box. So the honest-box work (borders / gradients / radius /
  shadow) deliberately leaves the image path alone.

## Fix outline (deferred)

1. Capture the resolved image URI (and, where feasible, decoded pixels or a
   decode handle) on the `HNode` / layout node during layout.
2. Populate the executor's `images` list from those captured resources (decode
   PNG/JPEG via the existing image decoders in `src/lib/common/image/`).
3. Emit `DRAW_IR_COMMAND_IMAGE` for `<img>` and `background-image` layers so the
   executor's existing `draw_image_scaled` branch paints them.

## Optional follow-up (design debt)

The current box styling is packed into `computed_style` key/value strings
(`background-image = "linear-gradient(<from>,<to>)"`, `box-shadow`,
`border-*-color/width`, `border-radius`) and re-parsed by the executor. A cleaner
design would add first-class Draw-IR ops (border / gradient / shadow / image)
instead of overloading `DRAW_IR_COMMAND_RECT` with style-string side channels.
Tracked here as a non-blocking follow-up.
