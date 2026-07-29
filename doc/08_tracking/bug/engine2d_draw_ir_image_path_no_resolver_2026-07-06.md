# Engine2D Draw-IR CSS background-image path has no resolver

- **ID:** engine2d-draw-ir-image-path-no-resolver-2026-07-06
- **Status:** Partially resolved (`<img>` fixed 2026-07-29; CSS background image open)
- **Area:** ui / gpu / engine2d / browser_engine
- **Date:** 2026-07-06

## Summary

The Engine2D advanced Draw-IR executor
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`) can render
`DRAW_IR_COMMAND_IMAGE` commands, but only when the caller supplies a matching
resolved bitmap through the `images: [Engine2dResolvedDrawIrImage]` list
(`engine2d_draw_ir_adv_batch_with_images` /
`engine2d_draw_ir_adv_composition_with_images`). The HTML layout renderer path
now receives bounded decoded external PNG resources for `<img>` through
BrowserSession and `SBRF5`. CSS `background-image: url(...)` still does not
populate that list.

## Why the image op is not emitted from HTML today

- `<img>` emits `DRAW_IR_COMMAND_IMAGE` after its box and resolves the authored
  `src` against `BrowserSession.image_resources`.
- BrowserSession fetches the resolved URL through CSP/HSTS/mixed-content policy,
  decodes a bounded PNG, and retains the authored `src` as the Draw-IR key.
- CSS `background-image: url(...)` still lacks URL discovery and resource
  binding.

## Fix outline (deferred)

1. Discover CSS URL image values during style resolution.
2. Route them through the existing BrowserSession image broker and resource
   bounds.
3. Emit the existing Draw-IR image command as a background paint layer.

## Optional follow-up (design debt)

The current box styling is packed into `computed_style` key/value strings
(`background-image = "linear-gradient(<from>,<to>)"`, `box-shadow`,
`border-*-color/width`, `border-radius`) and re-parsed by the executor. A cleaner
design would add first-class Draw-IR ops (border / gradient / shadow / image)
instead of overloading `DRAW_IR_COMMAND_RECT` with style-string side channels.
Tracked here as a non-blocking follow-up.
