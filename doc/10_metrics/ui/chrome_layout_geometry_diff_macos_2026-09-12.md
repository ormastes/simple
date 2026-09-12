# Chrome vs Simple CSS layout geometry differential — macOS, 2026-09-12

Tool: `scripts/check/check-chrome-layout-geometry-diff.shs` +
`src/app/ui/chrome_showcase/layout_geometry_diff.spl` (spec:
`test/01_unit/app/ui/layout_geometry_diff_spec.spl`, `14 examples, 0 failures`;
`--selftest` = `SELFTEST PASS — 4 fixture(s) checked`).
Chrome 152.0.7977.83 `--headless=new --window-size=900,760
--virtual-time-budget=2000 --dump-dom` over a walker-injected copy of each page;
Simple side is `web_render_backend("pure_simple", 900, 760).render_html_to_draw_ir`.
Both sides key on the SAME body-relative nth-path over layout elements
(`_simple_web_node_target_key`, `..._renderer.spl:122`). Interpreter
`build/cargo-r2/release/simple` (`39368072 1789171430`).
Tolerance 1 px. Verdict: **PASS — 158 element(s) compared, 136 mismatched.**

Chrome headless 152 does not exit after `--dump-dom` on this host; the harvest is
wrapped in `timeout`, which is why the gate is time-bounded rather than hanging.

## Per page

| page | Chrome elements | Simple boxes compared | mismatched (root / inherited) | no Simple box |
|---|---|---|---|---|
| overview | 23 | 18 | 14 (14 / 0) | 0 |
| html | 431 | 28 | 21 (15 / 6) | 403 |
| css-layout | 401 | 23 | 22 (21 / 1) | 378 |
| css-paint | 158 | 25 | 24 | 133 |
| forms-media | 176 | 27 | 24 | 149 |
| animation | 122 | 24 | 22 | 98 |
| evidence | 4 | 4 | 0 | 0 |
| tab-bar | 9 | 9 | 9 | 0 |

**Bug 0 — and the reason every other count is small: the Draw IR emits a box for
only ~6 % of the laid-out document on a long page.** Layout itself runs for every
box (a temporary per-call counter at `..._layout.spl:1346` recorded 772 calls
over 772 distinct indices on css-layout), but only 52 Draw IR commands come out,
all above the fold. Everything below `y≈760` is dropped before emission, so the
pixel gate and this differ are both blind to 94 % of the page. Suspect: the
viewport clip applied during Draw IR build in
`simple_web_html_layout_renderer_paint_layout.spl`. Until this is fixed no
geometry gate over the catalog can be considered non-vacuous.

## Ranked CSS-feature bug list (root mismatches, all 8 pages)

| rank | feature | root Δ | first offending element | Δ (x,y,w,h) | suspected site |
|---|---|---|---|---|---|
| 1 | **box-sizing / block height** | 70 | `overview path:0` `<main>` | 0,0,0,**43** | `..._layout.spl` `css_outer_height` — content height accumulates one extra line box; every block ancestor inherits the 43 px |
| 2 | **inline flow x-position** | 25 | `overview path:0/0/2/0` `<strong>` | **28**,4,7,6 | `..._layout.spl:504 inline_text_advance_width` / `:583 text_line_aligned_x` — inline boxes start at the line-box origin, not after the preceding inline run; dw≈0 while dx grows 28→55 across siblings, so this is flow positioning, not font metrics |
| 3 | **flex item main size** | 11 | `overview path:0/0/4/0` `<ol>` | 0,1,**677**,0 | `..._layout.spl:1989-1996` (row-flex/wrap branch) with `:395 row_flex_distribution` — items get the container width instead of a max-content flex basis, so a wrapped row stacks like blocks (`<ul>` then lands 145,67 off) |
| 4 | **table row/cell** | 12 | `css-paint path:0/0/1/0` `<thead>` | 0,0,1,**43** | `..._layout.spl:800-858` `simple_web_collect_table_rows` — row-group heights are not summed into the table box (parent `<table>` is 128 px short) |
| 5 | **inline-block** | 8 | `forms-media` `<button>` | 2,8,**145**,9 | `..._layout.spl:504` — inline-block shrink-to-fit uses the line width rather than max-content; +8 px dy is the baseline (`vertical-align=baseline` not applied) |
| 6 | **grid item / grid** | 4 | `css-layout` grid container | — | `..._layout.spl:1743` — the grid branch is gated on `grid_columns.len() > 0`, so any grid without an explicit `grid-template-columns` (areas, implicit, `auto-flow`) silently falls through to block layout |
| 7 | position / overflow | 2 | `css-layout` sticky header | — | `..._renderer.spl:360 _simple_web_root_sticky_admitted` |

Inherited deltas (a child repeating all four of its parent's signed deltas) are
excluded from the ranking and reported separately — without that, one misplaced
flex container is counted once per descendant and dominates every bucket.

## Simple-only boxes

Simple emits `::marker` boxes as real children of `<li>` (4 on overview) and a
duplicate `path:` body box. These do not shift ordinals today (markers are last
children) but will the moment a marker is emitted first; worth a key-scheme note
rather than a fix.

Raw data: `build/chrome_layout_geometry_diff/<page>.geometry_diff.{sdn,md}`.
