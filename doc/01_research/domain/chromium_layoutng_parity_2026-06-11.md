# Chromium LayoutNG Parity Research

Date: 2026-06-11
Scope: MDI/Simple Web item 6, exact layout box comparison against modern Chromium.

## Primary Sources

- Chromium RenderingNG overview: https://developer.chrome.com/docs/chromium/renderingng
- Chromium LayoutNG deep dive: https://developer.chrome.com/docs/chromium/layoutng
- Chromium BlinkNG deep dive: https://developer.chrome.com/docs/chromium/blinkng
- CSSOM View `getBoundingClientRect()`: https://drafts.csswg.org/cssom-view/#dom-element-getboundingclientrect
- CSSOM `getComputedStyle()`: https://drafts.csswg.org/cssom/#dom-window-getcomputedstyle

## Findings

- LayoutNG was introduced by layout primitive rather than as a single atomic
  replacement. Block and inline layout reached stable use before later flex,
  grid, table, and fragmentation work. Simple parity should therefore stay
  primitive-scoped: block, padding, border, flex grow/shrink, wrapping, inline
  fragmentation, and text shaping need separate evidence rows.
- Chromium's current layout target is LayoutNG, not legacy Blink layout. Modern
  parity evidence should read current Chrome geometry and computed styles, not
  compare against stale legacy assumptions.
- LayoutNG uses immutable fragment output rather than the older mutable layout
  tree model. Copying Chromium layout code directly into Simple is not a small
  integration path because invalidation, fragment ownership, style resolution,
  and caching contracts are tied to Blink internals.
- Inline layout is fragment and line based. Exact parity for wrapped text,
  bidi, baseline, ascent/descent, and inline border/padding behavior cannot be
  proven by single border-box checks.
- `getBoundingClientRect()` is defined from client rects and returns a
  non-live border-area union. Geometry evidence must re-query the browser for
  each capture and must handle multi-fragment inline cases separately.
- `getComputedStyle()` returns resolved style values for supported properties.
  Border, padding, and background comparisons should use explicit longhand
  values from Chrome capture and Simple Draw IR computed-style fields.

## Implication For This Repo

The current best path is measured convergence:

1. Capture real Chrome/Electron `[data-geom-label]` geometry and computed
   style longhands.
2. Convert both browser and Simple Draw IR output into
   `StructuralLayoutBox`.
3. Require exact equality for border-box rect, padding, border width, and
   background color.
4. Keep text glyph raster, line metrics, bidi, and multi-fragment inline cases
   as separate tracked gaps until their own fragment-level evidence exists.

No blur, pixel tolerance, resolution downscaling, or copied browser pixels are
acceptable evidence for parity.
