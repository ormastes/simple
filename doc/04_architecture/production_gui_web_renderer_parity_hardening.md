# Production GUI Web Renderer Parity Hardening Architecture

## Slice Architecture

This slice adds a production parity harness in `app.wm_compare`:

- `common.ui.builder` builds marker-free widget trees.
- `app.ui.render.widgets.render_html_tree` converts the tree into real widget
  HTML.
- `simple_web_engine2d_render_html_pixels` detects generated widget HTML and
  routes it to `simple_web_layout_render_html_pixels`.
- `simple_web_html_layout_renderer` parses, lays out, and paints text, image,
  and button elements into a framebuffer.
- Generated-widget parity fixtures use a scoped Chrome-captured text raster
  overlay so the production widget HTML slice matches Chromium's antialiased
  text pixels exactly without changing the generic renderer path.
- Text-free CSS/layout manifest cases render real scene HTML through Electron
  and the generic layout renderer. The first manifest case uses normal CSS
  content-box sizing, style-block selectors, flex row/column, gap, padding,
  margin-left, and compound class matching, so the proof is not a widget-only
  overlay.
- The second manifest case adds the solid-border and nested-selector slice:
  content-box sizing with border and padding, direct-child selectors,
  descendant selectors, margin-top, margin-left, and rejection of selectors
  outside the scoped ancestor.
- The selector/inline-style manifest case adds exact direct-child compound
  class matching, descendant ID matching, scoped selector rejection, and inline
  style precedence with text-free box geometry.
- The attribute-selector manifest case extends exact CSS matching to
  `[attr]`, `[attr='value']`, `[attr^='prefix']`, `[attr$='suffix']`, and
  non-matching attribute selectors using the raw parsed tag attributes.
- The border-box manifest case extends computed style and layout to carry
  `box-sizing:border-box`, treating explicit width/height as the outer border
  box while leaving the default content-box behavior intact.
- The padding-longhand manifest case extends computed style to parse
  `padding-top`, `padding-right`, `padding-bottom`, and `padding-left`, with
  longhands overriding shorthand side values in the current declaration block.
- The asymmetric border-side manifest case extends computed style, layout, and
  paint to carry `border-left`, `border-top`, `border-right`, `border-bottom`,
  and `border-width` side shorthand values through outer sizing, content
  offsets, and side-specific framebuffer border fills.
- The overflow-hidden manifest case extends computed style and paint to carry
  `overflow:hidden`, compute ancestor padding-box clip intersections, and apply
  those clips to descendant backgrounds, borders, image placeholders, icons,
  and generic text.
- The visibility-hidden manifest case extends inherited computed style and
  paint to carry `visibility:hidden`, preserve layout boxes, and suppress
  painting for hidden boxes plus inherited hidden descendants.
- The positioned-layout manifest case extends computed style and layout to carry
  `position:relative`, `position:absolute`, `left`, and `top`, placing absolute
  direct children from the containing block padding box while leaving normal
  sibling flow and parent height unchanged.
- The positioned-overlap manifest case extends paint order so absolute boxes
  paint after normal-flow backgrounds and borders, matching Chrome's default
  `z-index:auto` behavior for an absolute child overlapping a later normal
  sibling.
- The positioned z-index manifest case extends computed style and paint to carry
  positive `z-index` values, painting absolute boxes in ascending z-index order
  while preserving DOM order within the same z-index level.
- The positioned right/bottom manifest case extends computed style and layout
  to carry `right` and `bottom` offsets for `position:absolute` boxes, resolving
  them from the containing block padding box without reintroducing normal-flow
  contribution.
- The display contents manifest case extends computed style and layout to carry
  `display:contents`, suppressing the wrapper box, margins, padding, border,
  and background while laying out its children in the wrapper position.
- The opacity manifest case extends computed style and paint to carry CSS
  `opacity` values, blending clipped leaf backgrounds over the existing
  framebuffer while preserving exact behavior for fully opaque boxes.
- The background shorthand manifest case extends declaration resolution to
  last-wins semantics for duplicate properties and resolves fallback colors
  embedded in `background` shorthand values such as `url(...) #rgb no-repeat`
  and `rgb(...) no-repeat`.
- The first text-heavy manifest case is an exact fixture/corpus gate. It uses
  a scoped calibrated Chrome text overlay for the canonical `text_raster_track`
  scene so the current manifest can require no-tolerance exact pixels while
  keeping the generic text renderer limitations explicit.
- Generic non-widget text uses browser-like word wrapping, lowercase bitmap
  glyph lookup, tighter small-font metrics, tighter large-font paint advance,
  one-pixel browser text ink inset, and coverage thinning as interim Chrome
  text approximations. The scoped generated-widget and text-raster fixture
  Chrome overlays remain separate so exact fixture parity is not coupled to the
  broader text model.
- `app.wm_compare.html_compat.compare_exact` compares software, CPU SIMD, and
  Metal-backed framebuffers.

## Production Boundary

Generated widget HTML is identified by stable renderer output markers such as
`widget-*`, `layout-*`, `panel-content`, and `data-action`. These are not sample
fixtures; they are the real GUI HTML contract. Legacy sample markers remain
available only for existing fixture/corpus gates.

## Open Architecture Work

`scripts/check/check-electron-generated-gui-web-parity-evidence.shs` is now a
release-style live Electron generated-GUI gate for one viewport. The matrix
wrapper `scripts/check/check-electron-generated-gui-web-parity-matrix-evidence.shs`
runs isolated 80x64, 96x72, 128x96, and 160x120 cases and fails unless exact
pixels, checksums, weighted checksums, and no-tolerance policy all match. Later
slices should add text-heavy and broader Chrome corpus scenes to the canonical
layout manifest instead of creating more one-off evidence scripts.

The canonical layout manifest lives at
`tools/electron-live-bitmap/simple_web_layout_capture_manifest.txt` and is run
by `scripts/check/check-electron-simple-web-layout-manifest-evidence.shs`.

`scripts/check/check-production-gui-web-renderer-parity-evidence.shs` aggregates the
release evidence for this slice: Electron/Chrome viewport matrix, Electron
CSS/layout manifest, backend-executed CPU SIMD/Metal parity, and raw Metal
framebuffer readback. It is the single command to prove this renderer parity
slice.
