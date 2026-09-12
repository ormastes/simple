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

All figures below are from the final run (`build/geomdiff_run3.log`); the
root/inherited split is read from each page's `.sdn`, not recounted by hand.

| page | compared | root mismatches | inherited | Chrome elements with no Simple box |
|---|---|---|---|---|
| overview | 18 | 9 | 5 | 0 |
| html | 28 | 16 | 5 | 403 |
| css-layout | 23 | 21 | 1 | 378 |
| css-paint | 25 | 22 | 2 | 503 |
| forms-media | 27 | 22 | 2 | 76 |
| animation | 24 | 20 | 2 | 57 |
| evidence | 4 | 0 | 0 | 0 |
| tab-bar | 9 | 8 | 1 | 0 |

**Bug 0 — and the reason every other count is small: the Draw IR emits a box for
only ~6 % of the laid-out document on a long page.** Layout itself runs for every
box (a temporary per-call counter at `..._layout.spl:1346` recorded 772 calls
over 772 distinct indices on css-layout), but only 52 Draw IR commands come out.

Cause **verified, not inferred** — the same page rendered at two viewport
heights: `viewport_h=760 commands=52 max_y=776` vs
`viewport_h=20000 commands=1040 max_y=14364`. It is a viewport clip in Draw IR
emission, not the render time budget (`_web_budget_rearm`) and not element class
(`<br>` accounts for 5 of the 378). Everything below the fold is dropped before
emission, so this differ, the catalog pixel gate, and any scrolled render are all
blind to ~94 % of a long page. Until it is fixed no geometry gate over the
catalog can be considered non-vacuous.

## Ranked CSS-feature bug list (root mismatches, all 8 pages)

There is deliberately no `box-sizing` bucket: `* { box-sizing: border-box }` is
near-universal in the catalog CSS, so classifying on it captured the largest
group while naming a property that cannot change an auto-height block's height.
Those 54 rows are block flow, and rank 1 is where they belong.

| rank | feature | root Δ | first offending element | Δ (x,y,w,h) | suspected site |
|---|---|---|---|---|---|
| 1 | **block auto-height** | 54 | `overview path:0` `<main>` | 0,0,0,**43** | `..._layout.spl:3018` `out_bh[i] = h` — the accumulated content height of a block is 43 px long on overview and 128 px on css-paint; every block ancestor then carries it |
| 2 | **inline flow x-position** | 25 | `overview path:0/0/2/0` `<strong>` | **28**,4,7,6 | `..._layout.spl:2660-2669` — `inline_x` advances per child from `inline_start_x`, and `out_bx[c] = ix + inline_x`; dw≈0 while dx grows 28→55 across five siblings, so the advance is short per run: flow positioning, not font metrics |
| 3 | **flex item main size** | 12 | `overview path:0/0/4/0` `<ol>` | 0,1,**677**,0 | `..._layout.spl:1989-1996` (row-flex/wrap branch) with `:395 row_flex_distribution` — items take the container width instead of a max-content flex basis, so a wrapped row stacks like blocks and the following `<ul>` lands 145,67 off |
| 4 | **table row/cell** | 10 (+1 table) | `css-paint path:0/0/1/0` `<thead>` | 0,0,1,**43** | `..._layout.spl:800-858` `simple_web_collect_table_rows` / `:1734 out_bh[i] = table_h` — row-group heights are not summed into the table box (the `<table>` is 128 px short) |
| 5 | **inline-block** | 8 | `forms-media` `<button>` | 2,8,**145**,9 | `..._layout.spl:2660-2669` — inline-block shrink-to-fit takes the line width rather than max-content; the +8 px dy is `vertical-align: baseline` not being applied |
| 6 | **grid item / grid** | 4 | `css-layout` grid container | — | `..._layout.spl:1743` — the grid branch is gated on `grid_columns.len() > 0`, so a grid with no explicit `grid-template-columns` (areas, implicit, `auto-flow`) silently falls through to block layout |
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
