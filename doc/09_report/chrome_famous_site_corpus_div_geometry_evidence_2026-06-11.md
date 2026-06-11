# Chrome Famous-Site Corpus Div Geometry Evidence

Date: 2026-06-11
Status: pass for focused smoke row

## Scope

This report covers one deterministic famous-site corpus row:
`site_0_google`.

It compares the generated fixture div from stored Chrome metrics against the
Pure Simple web renderer Draw IR. It does not claim full famous-site corpus
coverage, live-site coverage, text raster parity, or glyph antialiasing parity.

## Evidence

- Test:
  `test/03_system/gui/wm_compare/structural_layout_report_spec.spl`
- Helper:
  `src/app/wm_compare/site_corpus_layout_report.spl`
- Generated manual:
  `doc/06_spec/test/03_system/gui/wm_compare/structural_layout_report_spec.md`
- Chrome sidecar:
  `test/09_baselines/famous_site_corpus/site_0_google/chrome_metrics.json`

The executable scenario calls `build_site_corpus_div_geometry_report(sample,
metrics, 160, 120)` and requires:

- `status: "layout_match"`
- `source_a: "chrome_metrics_div"`
- `source_b: "simple_renderer_div"`
- `width: 120`
- `height: 40`
- `background_color: "rgb(37, 99, 235)"`

Temporary probe output before deletion showed both Chrome and Simple boxes at
`x=8`, `y=8`, `width=120`, `height=40`, with matching background color and
fixture text.

## Verification

Commands run:

```sh
/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple check \
  src/app/wm_compare/site_corpus_layout_report.spl \
  test/03_system/gui/wm_compare/structural_layout_report_spec.spl

SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple test \
  test/03_system/gui/wm_compare/structural_layout_report_spec.spl \
  --mode=interpreter --clean

/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple spipe-docgen \
  test/03_system/gui/wm_compare/structural_layout_report_spec.spl \
  --output doc/06_spec --no-index
```

Results:

- `simple check`: pass
- SSpec: 8 passed, 0 failed
- Docgen: generated the structural layout report manual; docgen emitted
  unrelated existing warnings and classified the source as a stub because there
  is no prose doc block.

## Remaining Work

- Emit or compare geometry artifacts for more famous-site corpus rows.
- Keep box geometry evidence separate from the known browser text
  metric/raster/compositing gap.
- Do not use blur, tolerance, downscaling, or captured-pixel overlays to claim
  layout parity.
