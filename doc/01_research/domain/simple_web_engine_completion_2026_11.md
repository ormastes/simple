# Domain Research: Simple Web Engine Completion (2026-11)

- **Date:** 2026-11-28
- **Scope:** CSS 2.2 Stacking Contexts, Chromium LayoutNG `LayoutUnit` & Intrinsic Sizing, CSS Gradients / `backdrop-filter` Backdrop Root, and Hosted Browser Event Loop Architecture.

## 1. CSS 2.2 Appendix E — Painting Order Within a Stacking Context
Per CSS 2.2 Appendix E ("Elaborate Description of Stacking Contexts"), descendants of a single stacking context paint strictly in 7 ordered layers back-to-front rather than raw DOM tree order:
1. Background and borders of the stacking-context element itself.
2. Child stacking contexts with negative `z-index` (most negative first).
3. In-flow, non-inline-level, non-positioned descendants (standard normal-flow block boxes: background color, background image, border).
4. **Non-positioned floats** (their background, borders, and descendants). Because Step 4 follows Step 3, non-positioned floats paint **above** overlapping normal-flow block backgrounds — even blocks that follow the float in DOM source order.
5. In-flow, inline-level, non-positioned descendants (text runs, inline spans, inline-blocks, inline-tables), rendering **above** non-positioned floats.
6. Positioned descendants / child stacking contexts with stack level `0` (`z-index: 0` / `auto`).
7. Child stacking contexts with positive `z-index` (least positive first).

**Application to Simple Web Engine:** Both Draw IR (`_html_draw_ir_node_paint_order`) and software raster (`_paint_passes` Pass 1) must partition non-positioned float subtrees into Step 4 after normal-flow block backgrounds (Step 3) and before inline content/outlines.

## 2. Chromium LayoutNG `LayoutUnit` (`1/64` CSS px) & Inline Pen Precision
- Blink/LayoutNG represents layout coordinates and widths in fixed-point `LayoutUnit` multiples of `1/64` CSS pixel (`6` fractional bits).
- Inline items (`NGInlineItem`) convert floating/font-unit glyph advance sums into `LayoutUnit` via `LayoutUnit::FromFloatCeil` so subpixel accumulation never wraps prematurely or shifts subsequent item pen origins by `1/128` px across quarter-pixel LCD phase ties.
- In Simple Web Engine, font-unit sums should preserve exact face units (`_text_pen_milli` / GCD step counts) and apply one consistent `1/64`-px ceil at the inline-item boundary (including edge-space items and `<button>` / `<input type=button|submit|reset>` labels scaled at device pixel ratio `k`).

## 3. CSS Grid / Flexbox Intrinsic Sizing (CSS Sizing Level 3 §5)
- During min-content / max-content track contribution calculations (e.g., `grid-template-columns: auto 1fr`), percentage margins (`margin-left: 10%`) and percentage paddings of descendants do **not** have a resolved containing-block width yet and must resolve to **`0`** intrinsically (only applied once the track's final used width is assigned).
- Nested `display:flex` containers inside `auto` grid items must contribute their flex items' intrinsic content sum (with `%` margins treated as `0`), never collapsing to container `available_w`.

## 4. CSS Images L3 (`radial-gradient`) & Filter Effects L2 (`backdrop-filter`)
- `radial-gradient()` defines a `circle` or `ellipse` ending shape centered at `<position>` with extent keywords (`closest-side`, `farthest-side`, `closest-corner`, `farthest-corner`), interpolating premultiplied RGBA color stops along the gradient ray.
- `backdrop-filter: blur() saturate() brightness()` reads only pixels within the nearest **Backdrop Root** boundary (triggered by `<html>`, `filter != none`, `opacity < 1`, `mask`/`clip-path`, `backdrop-filter != none`, or `mix-blend-mode != normal`) and filters/blurs the backdrop inside the clipped box before painting the element's own translucent fill and borders.

## 5. Interactive Browser Event-to-Render Loop Architecture
- Event handlers coalesce rapid input/resize bursts (`16 ms` frame tick / settled resize debounce) and translate physical window coordinates `(x, y)` into layout coordinates `(x / k, y / k + scroll_y)` for hit-testing against `DrawIrCommand.hit_rect` bounds (`<a href>`, `<button>`, `<input>`).
- Navigating (`href`), reloading, scrolling (`wheel`), or moving Back/Forward updates session history + scroll state and triggers a single re-layout/present pass in the top-level caller (`main.spl`) so JIT codegen stays active across the render pipeline.

## References
- W3C CSS 2.2 Appendix E (Stacking Context Painting Order)
- Chromium Blink `LayoutUnit` & `NGInlineItem` (`third_party/blink/renderer/platform/geometry/layout_unit.h`)
- W3C CSS Images Module Level 3 (`radial-gradient`) & CSS Filter Effects Module Level 2 (`backdrop-filter` / Backdrop Root)
- W3C CSS Box Sizing Level 3 §5 (Intrinsic Sizes & Percentage Margins)
