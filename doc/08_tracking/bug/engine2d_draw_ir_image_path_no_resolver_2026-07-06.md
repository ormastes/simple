# Engine2D Draw-IR CSS background-image path has no resolver

- **ID:** engine2d-draw-ir-image-path-no-resolver-2026-07-06
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Area:** ui / gpu / engine2d / browser_engine
- **Date:** 2026-07-06

## Summary

The Engine2D advanced Draw-IR executor
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`) can render
`DRAW_IR_COMMAND_IMAGE` commands, but only when the caller supplies a matching
resolved bitmap through the `images: [Engine2dResolvedDrawIrImage]` list
(`engine2d_draw_ir_adv_batch_with_images` /
`engine2d_draw_ir_adv_composition_with_images`). The HTML layout renderer path
now receives bounded decoded external PNG resources for `<img>` and static CSS
URL backgrounds through BrowserSession and `SBRF5`.

## Why the image op is not emitted from HTML today

- `<img>` emits `DRAW_IR_COMMAND_IMAGE` after its box and resolves the authored
  `src` against `BrowserSession.image_resources`.
- BrowserSession fetches the resolved URL through CSP/HSTS/mixed-content policy,
  decodes a bounded PNG, and retains the authored `src` as the Draw-IR key.
- Inline and linked CSS URL backgrounds reuse that broker/resource path. Layout
  emits typed size/position/repeat/origin/clip geometry behind content, and the
  hosted worker sends only composition-referenced images in `SBRF5`.

## Fix delivered

1. Discover bounded CSS URL image values from inline and linked static CSS.
2. Route them through existing BrowserSession image policy and PNG bounds.
3. Emit the existing Draw-IR image command as a typed background paint layer.
4. Prove exact transparent/repeat/position/content/border pixels plus HSTS,
   mixed-content, CSP, and referenced-resource filtering.

The existing animation scheduler and retained-frame timing remain unchanged.

## Dynamic follow-up delivered

Post-load JavaScript and Simple Script reconciliation rediscovers new background
URLs and reuses `_start_image_source`. CSP/HSTS/mixed-content, deduplication,
response generation, bounded PNG decode, retained resources, and Draw-IR
resolution stay on the static image path. Commit invalidates rendering without
restarting animation time; stopped or superseded loads reject late responses.

Pure-Simple runtime execution remains compiler-blocked, so focused source and
host evidence is not recorded as a browser runtime PASS.

## Optional follow-up (design debt)

The current box styling is packed into `computed_style` key/value strings
(`background-image = "linear-gradient(<from>,<to>)"`, `box-shadow`,
`border-*-color/width`, `border-radius`) and re-parsed by the executor. A cleaner
design would add first-class Draw-IR ops (border / gradient / shadow / image)
instead of overloading `DRAW_IR_COMMAND_RECT` with style-string side channels.
Tracked here as a non-blocking follow-up.
