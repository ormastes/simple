# Web ↔ Chrome layout-geometry parity — round 14 (2026-09-14)

**First 8-page baseline measured on an untruncated layout.** Rounds 11-13's
html / css-layout / css-paint / forms-media / animation figures were void for a
stale runner binary; this round found a *second*, independent reason they were
void (a wall-clock render budget that truncated every page) and fixed it. The
"deferred" note in `web_chrome_parity_baseline_fresh_runner_2026-09-14.md` is
superseded by the table below.

## Provenance

| | |
|---|---|
| tree | `37c0a963ec1` (on `a7a19a52182`, PR #963) |
| runner | `build/cargo-r2/release/simple`, mtime `Sep 14 08:34:50 2026`, sha256 `2d0669321ebbc805…` |
| Chrome | 152.0.7977.83, `--headless=new`, `--window-size=900,20000` |
| env | `SIMPLE_EXECUTION_MODE=interpreter`, `SIMPLE_TIMEOUT_SECONDS=0`, `GEOM_DIFF_HEIGHT=20000`, `SIMPLE_WEB_RENDER_BUDGET_MS=1200000`, `GEOM_DIFF_TIMEOUT_SECS=1800` |
| command | `sh scripts/check/check-chrome-layout-geometry-diff.shs` |

One tree, one binary, one Chrome harvest per page.

## Root cause found and fixed: the differ measured a deadline

`WEB_RENDER_BUDGET_MS = 10000`
(`simple_web_html_layout_renderer_foundation.spl:151`) is the **renderer's own**
wall-clock budget. Under the interpreter the style pass tripped it at **node 46
of 883** on `html.html`; every node past the break kept
`renderer_default_style()` and the whole Simple side came back as 432 boxes of
`(0,0,0,0)`. `SIMPLE_TIMEOUT_SECONDS` — which the harness already pinned, and
whose name invites the confusion — is the *runner's* timeout and does nothing to
it.

Same page, same binary, same Chrome harvest, only the budget changed:

| `SIMPLE_WEB_RENDER_BUDGET_MS` | compared | mismatched |
|---|---|---|
| unset (10 000 ms) | 431 | **430** (degenerate — every box zero) |
| lifted | 431 | **329** |

Fixes: the harness pins the budget; the differ **fails closed** on
`simple_web_layout_last_render_degraded()` so a truncated render can never again
be reported as a comparison (sabotage-proven at `…BUDGET_MS=1000`). Full record:
`doc/08_tracking/bug/web_render_budget_truncates_geometry_differ_layout_2026-09-14.md`.

## Second harness defect fixed: `<body>` was never compared

Chrome's `--dump-dom` emits the walker's first row on the same physical line as
the `<pre>` open tag (`</script><pre id="__geom__">GEOM|path:|body|…`), so the
harness's `grep '^GEOM|'` silently dropped it. That row is `<body>` — the one
row that would expose a UA body margin, a viewport-width error, or a differ
origin bug — and it surfaced instead as `missing_in_chrome: 1 path:(body)`,
i.e. as a *Simple-only* box. Fixed by anchoring the `sed` on the `<pre>` tag
rather than the line start.

**With the body row now compared, it MATCHES**: `evidence` goes 4/0 → 5/0 and
`overview` 18/5 → 19/5. Chrome's body on these pages is `0,0,900×h`. So the
residual mismatches are **not** an origin, root-margin, root-font-size, or
viewport-width problem — that whole family is eliminated by measurement, not by
argument.

## The 8-page table

Measured before the `<body>` harvest fix, so each page's `compared` rises by 1
next round and its `mismatched` is unaffected on the two pages where the body was
checked directly.

| page | compared | mismatched | root | inherited | dominant root feature |
|---|---|---|---|---|---|
| overview | 18 | 5 | 5 | 0 | inline (5) |
| html | 431 | 329 | 136 | 193 | block-flow (103), inline (31) |
| css-layout | 401 | 336 | 219 | 117 | block-flow (146), inline (72) |
| css-paint | 528 | 515 | 430 | 85 | block-flow (297), inline (127), table-cell (6) |
| forms-media | 103 | 102 | 22 | 80 | block-flow (12), inline-block (8) |
| animation | 81 | 79 | 50 | 29 | block-flow (31), inline (19) |
| evidence | 4 | **0** | 0 | 0 | — |
| tab-bar | 9 | 7 | 7 | 0 | flex-item (7) |
| **total** | **1575** | **1373** | | | |

`evidence` is clean. Every other page is dominated by one signature.

## The signature: vertical-only drift, on seven of eight pages

Counting **root** mismatches (a child merely carried by its parent's error is
excluded), how many have each delta component equal to zero:

| page | root rows | dx=0 | dy=0 | dw=0 | dh=0 |
|---|---|---|---|---|---|
| html | 136 | 135 | **1** | 119 | 103 |
| css-layout | 219 | 217 | **3** | 211 | 173 |
| css-paint | 430 | 424 | **2** | 416 | 306 |
| animation | 50 | 45 | **1** | 45 | 39 |
| forms-media | 22 | 14 | **3** | 11 | 8 |
| overview | 5 | 1 | 0 | 4 | 5 |
| tab-bar | 7 | 1 | **7** | 0 | 7 |

Horizontal geometry is essentially correct and box sizes largely are too;
**almost every root mismatch is a vertical-position error**. `tab-bar` is the
one exception and is the mirror image — `dy` is right on all 7 rows and every
`dw` is wrong, all classified `flex-item`. That is a separate cluster.

`dy` is *not* proportional to `y` (the ratio falls down the page), so this is not
a scale factor. It is flat across runs of consecutive elements and then **steps
by ~16 px**, accumulating: on `html`, `dy` = 17 → 33 → 49 → … Each occurrence of
some construct is ~16 px too short in Simple, and everything below inherits the
running total — which is exactly why 193 of html's 329 mismatches classify as
*inherited*. The first step on `html` lands inside an `<li>` between an inline
`<code>` run and the block `<div>` that follows it, i.e. at the **anonymous
block box** CSS requires there. Characterised, with the next diagnostic step, in
`doc/08_tracking/bug/web_layout_vertical_drift_accumulates_16px_per_construct_2026-09-14.md`.

## What is left

1. The ~16 px vertical accumulation (open bug above) — the single largest
   cluster on 6 of 8 pages. Needs a minimal `<li><code/><div/></li>` fixture to
   separate "anonymous block line-height" from "missing UA vertical margin"
   before anything is changed.
2. `tab-bar`'s flex-item width cluster (7/7 rows), untouched by (1).
3. Re-baseline once (1) lands; the table above is the pre-fix reference.
