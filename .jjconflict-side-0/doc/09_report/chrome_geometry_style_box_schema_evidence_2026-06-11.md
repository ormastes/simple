# Chrome Geometry Style Box Schema Evidence

Date: 2026-06-11
Status: Pass for focused schema smoke

## Scope

This evidence covers the focused Chromium geometry access path for non-text CSS
box metadata. It does not claim full layout parity for every manifest row and
does not address glyph antialiasing or font metrics.

## Commands

```sh
node --check tools/chrome-live-bitmap/capture_html_argb.js
node --check tools/electron-live-bitmap/capture_html_argb.js
SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/gui/wm_compare/electron_geometry_compare_spec.spl --mode=interpreter
CHROME_CAPTURE_HTML=test/fixtures/html_compat/07_scrollable_list.html \
CHROME_CAPTURE_WIDTH=120 \
CHROME_CAPTURE_HEIGHT=80 \
CHROME_CAPTURE_OUTPUT=build/chrome_style_geom_smoke/captured.json \
CHROME_CAPTURE_PROOF_PATH=build/chrome_style_geom_smoke/proof.json \
CHROME_CAPTURE_GEOMETRY_OUTPUT=build/chrome_style_geom_smoke/geometry.json \
node tools/chrome-live-bitmap/capture_html_argb.js
```

## Result

```text
chrome_capture_status=pass
chrome_capture_reason=pass
mismatch_count=0
geometry_written=true
blur_or_tolerance_used=false
scroll_shell|12|12|68|38|4|4|0|0|rgb(248, 250, 252)
scroll_list|16|16|45|40|0|0|0|0|rgba(0, 0, 0, 0)
scroll_item_0|16|16|42|8|0|0|0|0|rgb(219, 234, 254)
```

The pipe-delimited sample is:

```text
label|x|y|width|height|paddingLeft|paddingTop|borderLeft|borderTop|backgroundColor
```

## Interpretation

Chrome and Electron geometry capture now emit the same style-box schema for
`[data-geom-label]` nodes: border-box rect, computed padding, computed border
widths, background color, and normalized text. The Simple-side parser preserves
those fields in `StructuralLayoutBox`, and structural comparison treats a style
field mismatch as `layout_mismatch`.

This is exact structured evidence. It does not use blur, downscaling, pixel
tolerance, copied Chromium pixels, or text antialiasing normalization.
