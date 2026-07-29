# Web style producer costs ~4 s/node on the interpreted lane — cell cannot go green

**Status:** open. **Severity:** blocks the web × headless showcase cell on linux-x86_64.
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
(style producer loop, `budget-break` at line ~1876).

## Symptom

```
SHOWCASE_RESOLUTION=480x360 bin/simple run examples/06_io/ui/web_render_file_gui.spl
→ [web-style-producer] budget-break at=6 of=151 (deadline exceeded by 6.7 s)
→ web_standards_showcase status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898
```

`blank-or-uniform` here is **uniform, not blank**: every pixel is identical and
non-black (the background clear), because styling aborted before any content
was resolved, so nothing was ever painted on top.

## Measurements (2026-07-29, seed `bin/simple run`, after shaper repair `941c1daeacf`)

| Budget | Nodes styled before break | Implied cost | Wall |
|---|---|---|---|
| default | 6 of 151 | pre-style pipeline + 6 nodes ≈ budget + 6.7 s | 41.7 s (earlier baseline) / <60 s |
| `SIMPLE_WEB_RENDER_BUDGET_MS=120000` | 29 of 151 | **~4.1 s per node** | killed at 270 s, no status line, MAXRSS ~3.0 GB |

151 nodes × ~4 s ≈ 10 minutes of styling alone — no budget value makes this
lane green; the per-node cost itself is the defect.

## What it is NOT

- **Not the glyph-rasterization cost fixed in `ca5dac5e398`.** PROVED: this
  renderer's style loop contains zero calls to `get_glyph_advance`,
  `measure_glyph_into`, or any font/glyph function (grep of
  `simple_web_html_layout_renderer_core.spl`). The glyph fix targeted the
  `text_layout`/`font_renderer` pipeline, which this browser engine does not
  use during styling. Any claim that `ca5dac5e398` fixes the web cell is wrong
  for this lane.
- **Not silent interpreted fallback.** 0 `[jit-fallback]` markers, 0
  `Unknown variable` lines in either run log.
- **Not the shaper parse blocker.** Fixed in `941c1daeacf`; the pipeline now
  runs end-to-end and reproduces checksum 1322071898 deterministically.

## Suspected cost center (unverified)

Per-node style resolution against `build_rule_buckets` output — likely
selector matching whose per-node work scales with total rules × selector
parts under the seed interpreter/JIT. Not yet profiled; next step is a
per-stage `[layout-trace]` timing run (`trace_stages`) or a per-thread utime
diff to attribute the 4 s within one node's resolution.

## Reproduce

```
SIMPLE_WEB_RENDER_BUDGET_MS=120000 SIMPLE_TIMEOUT_SECONDS=270 \
SHOWCASE_RESOLUTION=480x360 bin/simple run examples/06_io/ui/web_render_file_gui.spl
# watch: budget-break at=N of=151 — N ≈ budget_s / 4
```
