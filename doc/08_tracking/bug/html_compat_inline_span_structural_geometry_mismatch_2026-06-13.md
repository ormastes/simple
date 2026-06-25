# HTML Compat Inline Span Structural Geometry Mismatch

- Status: resolved
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

## Resolution

The Simple structural path now lays direct inline children in normal block flow
as a single inline run, and it uses raw text-node advance width so preserved
spaces contribute to following inline child placement. Focused evidence:

```sh
SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
BUILD_DIR=build/chrome_html_compat_geometry_01_inline_fix2 \
REPORT_PATH=build/chrome_html_compat_geometry_01_inline_fix2/report.md \
HTML_COMPAT_GEOMETRY_FIXTURES='01_inline_text' \
sh scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs
```

Result: `fixture_count=1`, `pass_count=1`, `fail_count=0`, and
`blur_or_tolerance_used=false`. The default all-pass Chrome geometry manifest
now includes `01_inline_text`.
