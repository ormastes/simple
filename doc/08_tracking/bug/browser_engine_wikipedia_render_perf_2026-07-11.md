# browser_engine: real-page software render is ~176s interpreted (248KB page); default 10s budget always degrades

- Status: open (degraded-output honesty fixed; perf itself remains)
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Found: 2026-07-11 (Wikipedia Main_Page render comparison vs Chrome headless)

## Measurements (aarch64 mac, interpreted via seed)
- Input: https://en.wikipedia.org/wiki/Main_Page saved HTML, 248,519 bytes.
- `simple_web_layout_render_html_software_pixels(html, 480, 360, 300000)`:
  completes in **~176-227s**, `degraded=false`, 9,548 non-white pixels, correct
  content flow (matches Chrome's unstyled file:// render structurally).
- Same call with the DEFAULT 10s budget: `degraded=true`. Before today's fix the
  output was **fully blank** (0 non-white px); after the staged-budget fix it
  paints partial content (~1.2-2.4k non-white px across runs).
- Timing split: parse + extract_css ~5-8s; `compute_styles` (O(nodes x rules)
  cascade) is the dominant remaining cost.

## What was fixed today (same file)
1. Single wall-clock deadline covered style+layout+paint; `compute_styles` ate
   the whole budget, so `layout()`'s entry guard zero-sized every box and paint
   drew nothing. Now the budget is partitioned (style <=70%, layout <=90%,
   paint =100% of the caller's budget, never extended) via `_web_budget_rearm`.
2. 4 of paint()'s 6 O(n) passes had no budget guard and burned 7-13s after
   expiry; guards added, and paint's slice is split so the text pass always
   gets a turn.

## Still open
- Raw throughput: ~176s for a 248KB page is ~3 orders of magnitude from
  usable. Needs the compiled (non-interpreted) path for the renderer module
  and/or algorithmic work on the cascade (rule bucketing already exists;
  per-node candidate sets are still large on real-world stylesheets).
- Budget overshoot: at a 60s budget the render still overruns by ~25% —
  `layout`/`paint` text/glyph inner loops check the clock only per node, unlike
  `compute_styles`' intra-node sampling.

## Repro
```
# fetch (host HTTPS fallback)
FETCH_URL="https://en.wikipedia.org/wiki/Main_Page" FETCH_OUT=/tmp/wiki.html \
  bin/simple run tools/pixel_compare/fetch_url_probe.spl
# render, default budget -> degraded partial; budget 300000 -> full, ~176s
PIXEL_HTML=/tmp/wiki.html PIXEL_W=480 PIXEL_H=360 PIXEL_OUT_JSON=/tmp/wiki.argb.json \
  bin/simple run tools/pixel_compare/render_and_save_simple.spl
```

## Quota-spec marginality (measured 2026-07-11 evening)

The quota test (`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_engine_budget_hardening_spec.spl`) "keeps the first stylesheet rule effective when total rules exceed the quota" is now intermittently flaking under machine load (load avg ~15, multiple concurrent agent sessions). It exercises 4300 CSS rules on 3 nodes within a 60s budget.

Stage timings via `simple_web_layout_render_html_software_pixels_traced` on the exact quota-test HTML (3 nodes, 4300 rules, 96×64):
- parse_html: 6–23ms
- extract_css: 2.4–5.9s
- compute_styles: **50–76s** (dominant cost; ~12–18ms per rule for interpreted preprocessing inside `build_rule_buckets` + `build_rule_specificities` + per-rule work)
- layout: 0–10ms
- paint: 3–7ms

When compute_styles exceeds the budget slice, the render correctly reports `degraded=true` and the body-background pixel assertion fails (white instead of #3050a0)—the failure is honest, just load-marginal.

The staged-budget change (style ≤70% of total budget) reduced the quota test's effective style budget from 60s to 42s, widening the flake window under load. Not a correctness bug—the test's "generous budget" assumption (60s >> work) no longer holds on a loaded interpreter.

Follow-ups to consider (do not implement): (a) raise the quota test's budget or lower its junk-rule count so intent (rule quota, not wall clock) is tested with margin; (b) reduce per-rule preprocessing cost (memoize specificity parsing); (c) count rule preprocessing against its own guarded sub-slice so a preprocessing overrun degrades earlier and cheaper.
