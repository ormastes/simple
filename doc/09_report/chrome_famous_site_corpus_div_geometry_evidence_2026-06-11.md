# Chrome Famous-Site Corpus Div Geometry Evidence

Date: 2026-06-11
Status: pass for full deterministic corpus through chunked wrapper

## Scope

This report covers all 132 deterministic famous-site corpus rows through the
chunked wrapper evidence path. The executable SSpec still keeps two six-row
smoke chunks as a fast regression check.

It compares the generated fixture div from stored Chrome metrics against the
Pure Simple web renderer Draw IR. It does not claim live-site coverage, text
raster parity, or glyph antialiasing parity.

## Evidence

- Test:
  `test/03_system/gui/wm_compare/structural_layout_report_spec.spl`
- Helper:
  `src/app/wm_compare/site_corpus_layout_report.spl`
- Generated manual:
  `doc/06_spec/03_system/gui/wm_compare/structural_layout_report_spec.md`
- Full-corpus wrapper:
  `scripts/check/check-famous-site-corpus-div-geometry-chunks.shs`
- Full-corpus generated report:
  `doc/09_report/famous_site_corpus_div_geometry_chunks_2026-06-11.md`
- Chrome sidecars:
  `test/09_baselines/famous_site_corpus/*/chrome_metrics.json`

The executable scenarios call `build_site_corpus_div_geometry_report(sample,
metrics, 160, 120)` for the single-row detailed report and
`build_site_corpus_div_geometry_summary(6, 160, 120)` and
`build_site_corpus_div_geometry_summary_range(6, 6, 160, 120)` for bounded
corpus summary chunks. The full-corpus wrapper runs
`site_corpus_div_geometry_summary_cli.spl` in separate six-row chunks. They
require:

- `status: "layout_match"`
- `summary: (offset: 0 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0 ...)`
- `summary: (offset: 6 selected: 6 matched: 6 mismatched: 0 missing_metrics: 0 ...)`
- Full wrapper summary: `corpus_count=132`, `chunk_count=22`,
  `pass_count=22`, `fail_count=0`
- `source_a: "chrome_metrics_div"`
- `source_b: "simple_renderer_div"`
- `width: 120`
- `height: 40`
- `background_color: "rgb(37, 99, 235)"`

The SSpec two six-row summaries prove the fast regression path. The full
wrapper proves all 132 stored corpus rows in separate bounded Simple processes.
The single-row detailed report also shows both Chrome and Simple boxes at
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

SIMPLE_BIN=/home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple \
  scripts/check/check-famous-site-corpus-div-geometry-chunks.shs
```

Results:

- `simple check`: pass
- SSpec: 10 passed, 0 failed
- Full chunk wrapper: pass, `corpus_count=132`, `chunk_count=22`,
  `pass_count=22`, `fail_count=0`, `blur_or_tolerance_used=false`
- Docgen: generated the structural layout report manual; docgen emitted
  unrelated existing warnings and classified the source as a stub because there
  is no prose doc block.

## Remaining Work

- Fix the current unbounded/single-call aggregate runtime crash. Local probes
  on 2026-06-11 showed `build_site_corpus_div_geometry_summary(7, 160, 120)`,
  `(...12...)`, `(...24...)`, and `(...0...)` can segfault under
  `simple run`, while the chunked wrapper covers all 132 rows by running each
  six-row chunk in a separate Simple process.
- Keep box geometry evidence separate from the known browser text
  metric/raster/compositing gap.
- Do not use blur, tolerance, downscaling, or captured-pixel overlays to claim
  layout parity.
