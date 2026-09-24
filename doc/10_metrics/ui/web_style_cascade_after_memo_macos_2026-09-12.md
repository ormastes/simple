# Web style stage after the cascade memo + font-advance fix, macOS M4 (2026-09-12)

Binary `build/cargo-r2/release/simple`, `stat -f '%z %m'` = `39368072 1789171430`,
identical for every run below. `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_2D_BACKEND=cpu_simd SIMPLE_WEB_PHASE_TRACE=1`.
Provenance, stated exactly: `css-layout` and `animation` were rendered from the
worktree BEFORE any edit landed; the other six from a pristine `git archive HEAD`
tree under `/tmp/claude-501/before_tree`, so the edited `src/lib` could not reach
either set. Verified rather than assumed — `grep -l style_memo before.*.log` is
empty, and that print exists only in the edited tree. `css-layout` did not trip
the render budget on either side, so its numbers are full 908-node passes;
**`css-paint` and `html` DID trip it on the before side** (`grep -c budget-break`
= 1 each), so on those two pages the after run styles nodes the before run never
reached and a pixel difference there would have been expected, not a regression
(in the event both still came out byte-identical).

## The filed attribution was wrong — measured, not argued

`doc/08_tracking/bug/web_style_cascade_apply_decls_reparses_per_node_2026-09-12.md`
attributed 18,000-22,700 ms of a 25,229 ms style stage to `apply_decls`
re-parsing declaration text per node. Level-gated counters
(`SIMPLE_WEB_STYLE_COUNTERS=1`, `[web-phase] style_counters`) over the same page,
untruncated, say otherwise:

| leaf | calls | ms | share of the 30,041 ms style stage |
|---|---|---|---|
| per-`#text` font metric resolution | 146 | **26,887** | **90%** |
| ... of which `measure_text_advances` | 146 (2,601 chars) | 24,141 | 80% |
| whole author cascade (accumulate + apply + resolvers) | — | 1,029 | 3% |
| `decl_table_build` | 2,190 | 461 | 1.5% |
| `selector_group_matches_node_parts` | 1,045 | 283 | 0.9% |
| `apply_decls` full-probe body | 44 | **165** | **0.5%** |
| inherit + tag defaults | — | 588 | 2% |

`apply_decls` is 165 ms, not 18-23 s. 2,601 characters cost 24,141 ms of glyph
measurement — **9.3 ms per character** — because the module-level ASCII advance
cache held exactly ONE `(face identity, font_size)` pair and wiped its 95-entry
table on every size change, so a page mixing heading/body/code sizes thrashed it
and each character fell through to the SFFI-dylib backend's full pixel rasterize.

## Effect of the changes (css-layout.html, 908 nodes, 900x760)

| stage | before | after | |
|---|---|---|---|
| style | **29,379 ms** | **11,591 ms** | 2.5x |
| Draw IR build (compose/shaping) | 3,439 ms | 233 ms | 14.8x |
| pipeline to compose_shaping | 34,232 ms | 13,722 ms | 2.5x |

Cascade memo: 493 hits / 22 misses (96%). Font front memo: 247 hits / 146 misses.
Raising the advance cache from 8 to 32 slots was measured and changed nothing
(13,084 vs 13,118 ms), so 8 is kept.

## Target not met, and the named reason

The task's target was style <= 2,500 ms. At 11,591 ms it is not met. The residual
is still the same leaf: `measure_text_advances` is 5,346 ms for those same 2,601
characters (2.05 ms/char) with a warm advance cache, so the per-character path —
`horizontal_kern` runs per character PAIR and is not cached at all, and the
dylib-without-blob backend still has no metrics-only entry point — is the next
lever. That is font-lane work in `font_renderer.spl`, not style-engine work;
filed on the bug record rather than attempted here.

## Per-page cold stage split

| page | nodes | style before | style after | pipeline before | pipeline after |
|---|---|---|---|---|---|
| css-layout | 908 | 29,379 | 11,591 | 34,232 | 13,722 |
| css-paint | 1,200 | 29,442 | 8,875 | 31,275 | 10,875 |
| html | 836 | 29,672 | 10,096 | 34,684 | 11,295 |
| animation | 179 | 11,078 | 4,481 | 11,458 | 4,821 |
| forms-media | 225 | 9,273 | 4,422 | 9,745 | 4,822 |
| overview | 43 | 4,443 | 2,771 | 4,639 | 2,877 |
| tab-bar | 19 | 1,959 | 1,336 | 2,118 | 1,424 |
| evidence | 9 | 1,783 | 1,465 | 1,839 | 1,510 |

## Pixel oracle

Per-page PPM comparison (`cmp` byte-for-byte, then
`node tools/pixel_compare/diff_ppm.js` for any page that differs):

All eight pages are **byte-identical**, `mismatch=0` each: css-layout, animation,
css-paint, evidence, forms-media, html, overview, tab-bar. `cmp` reported no
difference on any page, so `diff_ppm.js` was never reached — the stronger result,
since byte identity implies zero differing pixels. Note this holds even for the
two pages whose before-run tripped the render budget, where a difference would
have been defensible.

No frame-total line exists in this trace — the last phase boundary is
`compose_shaping` — so no cold-frame total is claimed here. Raster is unchanged
by this work and out of scope.

## Appendix (2026-09-12, F14): the residual measurement leaf, measured

The "Target not met, and the named reason" section above named two suspects for
the 5,346 ms residual — uncached per-pair `horizontal_kern`, and a missing
metrics-only entry point on the dylib backend — and said so by elimination
rather than measurement. Direct counters say both are wrong, and name a third:

| leaf | calls | ms | share of the measurement leaf |
|---|---|---|---|
| advance-cache misses | 108 | 3,442 | 89% |
| ... the cmap re-parse inside them | 216 | 3,341 | 87% |
| `horizontal_kern`, all calls, uncached | 2,455 | **26** | **0.7%** |
| rasterize-for-metrics | **0** | **0** | **0%** |

Resolving one codepoint to a glyph id re-parses the entire cmap (segment arrays
plus the whole glyph-id array) at 15 ms a lookup, paid twice per miss — once by
`has_glyph`, once by the advance. Fixed with a batched one-parse cmap entry
point and a per-face ASCII glyph-id table.

| page | `measure_text_advances` | style | pipeline |
|---|---|---|---|
| css-layout | 3,946 -> **450 ms** | 9,493 -> 5,685 ms | 10,406 -> 6,546 ms |
| overview | 2,251 -> **188 ms** | 2,805 -> 733 ms | 2,874 -> 805 ms |

Both pages' PPMs are byte-identical before vs after (`cmp`, 0 mismatches).

**Measurement correction that applies to the tables above too:** the 13,084 /
13,291 ms style and 5,346 ms measure figures were COLD first-process runs. The
same unmodified tree, run warm, gives ~9,500 ms style and ~3,900 ms measure. The
F14 before/after pairs here are warm-vs-warm, both sides rendered from a
pristine `git archive HEAD` tree. Detail:
`doc/08_tracking/bug/web_text_measurement_kern_uncached_2026-09-12.md`.
