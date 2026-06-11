# Chrome Famous-Site Corpus Div Geometry Evidence

Date: 2026-06-11
Status: pass for bounded first-twelve-row corpus smoke

## Scope

This report covers the first twelve deterministic famous-site corpus rows:
`site_0_google`, `site_1_youtube`, `site_2_facebook`,
`site_3_instagram`, `site_4_x`, `site_5_tiktok`, `site_6_wikipedia`,
`site_7_amazon`, `site_8_reddit`, `site_9_netflix`, `site_10_linkedin`,
and `site_11_microsoft`.

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
- Chrome sidecars:
  `test/09_baselines/famous_site_corpus/site_0_google/chrome_metrics.json`
  through
  `test/09_baselines/famous_site_corpus/site_11_microsoft/chrome_metrics.json`

The executable scenarios call `build_site_corpus_div_geometry_report(sample,
metrics, 160, 120)` for the single-row detailed report and
`build_site_corpus_div_geometry_summary(6, 160, 120)` and
`build_site_corpus_div_geometry_summary_range(6, 6, 160, 120)` for bounded
corpus summary chunks. They require:

- `status: "layout_match"`
- `summary: (offset: 0 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0 ...)`
- `summary: (offset: 6 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0 ...)`
- `source_a: "chrome_metrics_div"`
- `source_b: "simple_renderer_div"`
- `width: 120`
- `height: 40`
- `background_color: "rgb(37, 99, 235)"`

The two six-row summaries prove each checked row reports `layout_match`. The
single-row detailed report also shows both Chrome and Simple boxes at `x=8`,
`y=8`, `width=120`, `height=40`, with matching background color and fixture
text.

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
- SSpec: 10 passed, 0 failed
- Docgen: generated the structural layout report manual; docgen emitted
  unrelated existing warnings and classified the source as a stub because there
  is no prose doc block.

## Remaining Work

- Extend the bounded summary to more famous-site corpus chunks or emit per-row
  geometry artifacts for the whole corpus.
- Fix the current unbounded/single-call aggregate runtime crash. Local probes
  on 2026-06-11 showed `build_site_corpus_div_geometry_summary(7, 160, 120)`,
  `(...12...)`, `(...24...)`, and `(...0...)` can segfault under
  `simple run`, while `site_6_wikipedia` passes as an individual row and
  two separate six-row chunks pass under SSpec.
- Keep box geometry evidence separate from the known browser text
  metric/raster/compositing gap.
- Do not use blur, tolerance, downscaling, or captured-pixel overlays to claim
  layout parity.
