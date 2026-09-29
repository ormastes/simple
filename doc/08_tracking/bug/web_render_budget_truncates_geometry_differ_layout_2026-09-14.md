# The web render budget truncated every geometry-differ layout (2026-09-14)

Status: **FIXED** (harness pinned + differ fails closed). Round 14.

## Symptom

With the FRESH runner binary (`build/cargo-r2/release/simple`, sha `2d066932…`,
the one round 13 deployed to cure the missing-extern all-zero shape), the
`html` page of the Chrome layout-geometry differ still produced a Simple side of
**432 boxes, every one of them `(0,0,0,0)`**:

```
chrome_boxes=431
simple_boxes=432
ERROR — nothing was checked (every Simple box is 0x0 at 0,0 ...)
```

So the round-13 diagnosis ("stale runner binary, missing
`rt_engine2d_blend_cov_span_u32`") was real but was **not the only** cause of the
all-zero shape, and fixing the binary did not cure it. The recorded round-13/14
baseline figure for html — 431 compared / 430 mismatched, i.e. essentially every
element differing — is a measurement of this, not of CSS.

## Root cause

The web renderer arms its own **wall-clock render budget**,
`WEB_RENDER_BUDGET_MS = 10000`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:151`),
enforced by `_web_budget_expired()` at every per-node loop. Under the
interpreter the per-node style pass is far slower than a frame deadline
assumes, so the style producer broke at **node 46 of 883**:

```
[web-style-producer] budget-break at=46 of=883 now_us=10100089 deadline_us=10000000
```

Every node past the break keeps `renderer_default_style()`; layout then emits
nothing and the whole document collapses to zero-sized boxes at the origin.

`SIMPLE_TIMEOUT_SECONDS=0` — which the differ harness already pinned, and whose
name invites exactly this confusion — is the **runner's** timeout and does
nothing to the render budget. The budget has its own override,
`SIMPLE_WEB_RENDER_BUDGET_MS`
(`..._foundation.spl:196`), which nothing in the differ lane ever set.

## Evidence (one tree, one binary, one Chrome harvest)

Same `html.geom.txt`, same runner, only the budget changed:

| `SIMPLE_WEB_RENDER_BUDGET_MS` | compared | mismatched |
|---|---|---|
| unset (10 000 ms default) | 431 | **430** (degenerate — all-zero side) |
| `1800000` | 431 | **329** (root 136, inherited 193) |

329 is the pre-stale figure the earlier rounds recorded, which is the
independent confirmation that the budget, not a regression, produced 430.

## Fix

1. `scripts/check/check-chrome-layout-geometry-diff.shs` exports
   `SIMPLE_WEB_RENDER_BUDGET_MS` (default `1800000`) beside the two env vars it
   already pinned, with the rationale inline. This does **not** raise the
   product default — the foundation comment forbidding that is about real
   renders, where the interpreter-vs-budget gap is a perf defect that must stay
   visible. A differ run is not a frame; a deadline-truncated layout is not a
   layout.
2. `src/app/ui/chrome_showcase/layout_geometry_diff.spl` now **fails closed** on
   `simple_web_layout_last_render_degraded()` before it compares anything, and
   names the env var in the message. This is the durable half: the break need
   not be total. A break at node 800 of 883 leaves a plausible-looking table
   that is still a measurement of the deadline, and nothing upstream would
   notice.

Sabotage proof (`SIMPLE_WEB_RENDER_BUDGET_MS=1000`):

```
ERROR — nothing was checked (the Simple render for .../html.html tripped its
wall-clock render budget (deadline-exceeded); the layout is truncated, not
slow. Raise SIMPLE_WEB_RENDER_BUDGET_MS — SIMPLE_TIMEOUT_SECONDS does NOT
disable the render budget)
```

## Not a defect (ruled out on the way)

`[web-style-producer] css-props-stage1 ... collected_len=0` and the matching
stage-2 line fire on `html.html` because the page's `<style>` block declares no
`:root` custom properties. The receipts are documented as silent only when a
block yields properties; they are diagnostics, not failures.

## Consequence for the metrics

Every html / css-layout / css-paint / forms-media / animation number recorded in
rounds 11-14 before this fix is void for a second, independent reason. The
round-14 table in `doc/10_metrics/ui/web_chrome_parity_round14_2026-09-14.md`
is the first one measured with an untruncated layout.
