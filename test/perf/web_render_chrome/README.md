# Chrome vs Simple Web Renderer Performance Comparison

Benchmark harness comparing the Simple web renderer against Chrome across four
HTML fixtures: static page, scroll-heavy, layout-stress, and paint-heavy.

## NFR 2B Requirements

- Simple p95 frame time must stay under **16.7 ms** for 60 Hz scroll targets.
- Chrome comparison reports must include **pixel compatibility** and **timing status**.
- Reports include `simple_vs_chrome_ratio`, pixel diff/hash, and PASS/WARN/FAIL.

## File Structure

```
test/perf/web_render_chrome/
  fixtures/
    static_page.html     — headings, paragraphs, images, cards
    scroll_heavy.html    — 20-section scrolling page with mixed content
    layout_stress.html   — nested flex/grid, tables, absolute positioning
    paint_heavy.html     — gradients, shadows, transforms, backdrop-filter
  artifacts/             — generated at runner time (not committed)
    chrome_<fixture>.json
    simple_<fixture>.json
  chrome_runner.spl      — Chrome DevTools Protocol fixture runner
  simple_runner.spl      — Simple renderer fixture runner
  trace_normalizer.spl   — Merge artifacts into normalized records
  report_spec.spl        — BDD spec: shape, threshold math, NFR 2B assertions
  README.md
```

## Running

```bash
bin/simple test test/perf/web_render_chrome/report_spec.spl
bin/simple run test/perf/web_render_chrome/simple_runner.spl
bin/simple run test/perf/web_render_chrome/chrome_runner.spl
bin/simple run test/perf/web_render_chrome/trace_normalizer.spl
```

## Status Thresholds

| Metric | PASS | WARN | FAIL |
|---|---|---|---|
| simple_frame_ms p95 | <= 15.0 ms | <= 16.7 ms | > 16.7 ms |
| simple_vs_chrome_ratio | <= 1.5x | <= 2.0x | > 2.0x |
| pixel_match_pct | >= 99% | >= 95% | < 95% |
| source == "synthetic" | always PENDING | | |

## Report Fields

`fixture`, `simple_frame_ms`, `chrome_frame_ms`, `simple_vs_chrome_ratio`,
`pixel_hash_simple`, `pixel_hash_chrome`, `pixel_match_pct`,
`parse_ms`, `style_ms`, `layout_ms`, `paint_ms`, `composite_ms`, `present_ms`,
`chrome_fps`, `chrome_dropped_frames`, `chrome_gpu_raster_ms`, `chrome_memory_mb`,
`source` (`"synthetic"` or `"measured"`), `status` (`PASS`/`WARN`/`FAIL`/`PENDING`).

## Promoting to Measured

Artifacts start as `source: "synthetic"` — spec accepts PENDING (no fake greens).
To promote: wire the DevTools bridge in `chrome_runner.spl` and the renderer
pipeline in `simple_runner.spl`, then set `source: "measured"` in the JSON.
