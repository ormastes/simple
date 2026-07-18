# Famous-Site Corpus Div Geometry Unbounded Summary Segfault

Date: 2026-06-11
Status: resolved-current-runtime

## Summary

The famous-site corpus div geometry path can compare individual rows and
bounded six-row chunks exactly, but larger single-call summaries can segfault
under `simple run`.

This is a runtime/evidence aggregation blocker, not a known geometry mismatch.
`site_6_wikipedia` matched individually, two six-row chunks covering rows 0-11
passed under SSpec, and the chunked wrapper covers all 132 rows by running each
six-row chunk in a separate Simple process.

## Reproduction

Temporary local probes on 2026-06-11 called:

```simple
build_site_corpus_div_geometry_summary(7, 160, 120)
build_site_corpus_div_geometry_summary(12, 160, 120)
build_site_corpus_div_geometry_summary(24, 160, 120)
build_site_corpus_div_geometry_summary(0, 160, 120)
```

Each crashed with a segmentation fault under:

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/src/compiler_rust/target/release/simple run tmp_probe_full_corpus_div.spl
```

The same worktree showed `build_site_corpus_div_geometry_report` for
`build_famous_site_sample_corpus()[6]` returning `status: "layout_match"`.

## Current Workaround

Use `scripts/check/check-famous-site-corpus-div-geometry-chunks.shs`, which
runs `site_corpus_div_geometry_summary_cli.spl` in separate bounded chunks.
The current executable spec covers offsets `0` and `6` as a fast regression
check.

## Current Status

Follow-up verification on 2026-06-11 shows the current runtime no longer
reproduces the single-process aggregate crash in this checkout:

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple \
  run src/app/wm_compare/site_corpus_div_geometry_summary_cli.spl \
  0 0 160 120 /tmp/full_div_geometry_limit0.sdn 132
```

Observed result:

```text
status=pass
offset=0
limit=0
expected=132
viewport_width=160
viewport_height=120
report_path=/tmp/full_div_geometry_limit0.sdn
```

The executable regression spec now covers the same all-row API:

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple \
  test test/03_system/gui/wm_compare/structural_layout_report_spec.spl \
  --mode=interpreter --clean --format json
```

Observed result: `11` passed, `0` failed.

No blur, downscaling, pixel tolerance, copied Chromium pixels, or text
antialiasing normalization is involved; the check compares stored Chromium DOM
metrics against Pure Simple Draw IR geometry.

## Remaining Guard

Keep the chunked wrapper as a fallback and release diagnostic, but do not treat
chunking as required when the full single-process `limit=0` regression spec and
CLI smoke are green.
