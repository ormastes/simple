# HTML Compat Inline Span Structural Geometry Mismatch

- Status: open
- Severity: P2
- Area: Simple Web Renderer / Chromium geometry parity
- Repro:
  `BUILD_DIR=build/chrome_html_compat_geometry_text_smoke REPORT_PATH=build/chrome_html_compat_geometry_text_smoke/report.md HTML_COMPAT_GEOMETRY_FIXTURES='01_inline_text' sh scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`

## Evidence

`01_inline_text` now has explicit `data-geom-label` markers so Chrome and
Simple can compare the same elements without pixel tolerance or blur. The
structural comparison fails honestly:

- Chrome `inline_para`: `x=8 y=16 width=304 height=18`
- Simple `inline_para`: `x=8 y=16 width=304 height=36`
- Chrome `inline_span`: `x=23 y=16 width=11 height=17`
- Simple `inline_span`: `x=8 y=34 width=304 height=18`

The current Simple structural path treats the labelled inline span as a block
box. Do not add `01_inline_text` to the default all-pass Chrome geometry
manifest until inline element layout produces Chromium-matching element
boundaries.
