# Famous-Site Corpus Div Geometry Unbounded Summary Segfault

Date: 2026-06-11
Status: open

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

## Required Fix

Investigate whether repeated `simple_web_layout_render_html_draw_ir` calls,
large string report concatenation, interpreter fallback, or module/runtime state
causes the crash. Full-corpus geometry evidence should not be promoted until a
single robust aggregation path or per-row artifact runner is available.
