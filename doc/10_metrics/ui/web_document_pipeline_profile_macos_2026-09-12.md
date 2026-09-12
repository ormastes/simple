# Web document pipeline profile — macOS, 2026-09-12

Interpreter: `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39368072 1789171430`), `SIMPLE_GPU_BACKEND=cpu_simd`,
viewport 900x760, 600 s timeout, one render per page (cold).
Instrument: the level-gated counters landed by PR #551/#559/#566 —
`SIMPLE_WEB_PHASE_TRACE=1 SIMPLE_WEB_STYLE_COUNTERS=1`. No temporary counters
were needed; the shipped ones already resolve to the leaf. Nothing under
`src/lib/**` was modified (`git diff --stat -- src/lib` is empty).

## Stage boundaries

| page | nodes | parse | style | layout | DrawIR/compose | total |
|---|---|---|---|---|---|---|
| `css-layout.html` | 908 | 648 ms | **5791 ms (78%)** | 762 ms | 211 ms | 7412 ms |
| `overview.html` | 43 | 45 ms | **867 ms (87%)** | 21 ms | 67 ms | 1000 ms |

Style dominates on both, and it is not the cascade: the author cascade is
935 ms of 5791 on the big page and 79 ms of 867 on the small one.

## Top 10 by self cost (css-layout.html / overview.html)

| # | leaf | ms (css-layout / overview) | calls | file:line | class |
|---|---|---|---|---|---|
| 1 | `resolve_font_metrics_with_language` (style-time font resolve) | **2940 / 713** | 146 / 15 | `simple_web_html_layout_renderer_core.spl:3295` → `font_renderer.spl:2964` | per-call fixed cost, no memo |
| 2 | `renderer.measure_text_advances` (inside #1) | 490 / 237 | 146 / 15 | `font_renderer.spl:2919` | per-char work (2601 chars / 490 ms) |
| 3 | author cascade `apply_decls` section | 935 / 79 | — | `..._core.spl:3199` (`_wsc_add_section(2)`) | O(nodes x decls) |
| 4 | parse (`parse_html` + `build_child_index`) | 648 / 45 | 1 | `..._renderer.spl:1813` | per-char / split-based |
| 5 | declaration-table build | 417 / 27 | 2190 / 119 | `..._foundation.spl:2534` | rebuilt per node, not per rule |
| 6 | `_html_text_language` | 511 / 11 | 146 / 15 | `..._core.spl:3278` | per-node ancestor scan |
| 7 | style inherit section | 530 / 18 | 908 / 43 | `..._core.spl:2958` (`section 0`) | whole-Style copy per node |
| 8 | selector matching | 256 / 11 | 1044 / 54 | `..._core.spl:2224` | 1 candidate/node — healthy |
| 9 | `.dispatch`/`probe` style helpers | 153 / 29 | 59 / 35 | `..._foundation.spl` | fixed |
| 10 | layout pass | 762 / 21 | 1 per box | `..._layout.spl` | linear, not a hotspot |

Memo health: cascade memo 493 hits / 22 misses (good); font-front memo
247 / 146 (63%); **shaped-run memo 0 hits / 146 misses — it never hits on
either page.**

## Algorithmic defects, named

Two hypotheses were tested and **refuted**, so they are recorded rather than
shipped as fixes:

- *Face reloading per text node.* `SIMPLE_WM_TRACE=1` on css-layout gives
  `from_cache=true` on 144 of 146 resolves — the face cache works.
- *Redundant re-layout.* A temporary per-call print at the entry of
  `layout_with_style` (`..._layout.spl:1346`, reverted; `git diff --stat --
  src/lib` clean) recorded **772 calls over 772 distinct box indices — exactly
  one layout per box.** There is no measure-then-layout double pass.

The real defects:

1. **The text content is walked or concatenated ~5 times per resolve**
   (`font_renderer.spl:2841-2910`), which is where 2450 ms of the 2940 ms sits
   (measurement itself is only 490 ms):
   `front_key` concatenates the whole content into a Dict key **before** the
   lookup (:2841); `text_codepoints(content)` decodes per char at :2860 **and
   again** at :2936 for `character_count`; `_resolved_font_complex_script`
   rescans the codepoints (:2861); `_resolved_font_metric_language_config_key`
   builds a second and third full-content key (:2872, :2906). All of it is
   per-char / string-building-in-a-loop work that is O(len) and repeated,
   including on the paths that then hit a cache.
2. **Per-node ancestor scan for language.** `_html_text_language` costs 3.5 ms
   per text node (`..._core.spl:3278`) — an O(depth) walk repeated per node
   rather than computed once per subtree.
3. **Declaration table rebuilt per node.** 2190 table builds for 908 nodes over
   a rule set that never changes (`..._foundation.spl:2534`), materialising
   3373 entries — string building in a loop.
4. **Whole-`Style` copy per node on inherit** (`..._core.spl:2958`), 530 ms for
   908 nodes; the struct carries 160+ fields and is copied, not shared.
5. **Style is the only superlinear stage.** 43 nodes → 867 ms, 908 nodes →
   5791 ms: 21x the nodes for 6.7x the time is sublinear per node, but the
   per-*text-run* cost (47 ms on overview, 20 ms on css-layout) is set by
   content length, not node count, so a page with long runs pays more than its
   node count predicts.

## Concrete fixes and expected saving (css-layout.html)

| fix | saving |
|---|---|
| Hash the content once per resolve and key all three caches on that hash instead of concatenating the full string three times | ~900 ms |
| Compute `text_codepoints(content)` once and pass it to both the complex-script scan and the `character_count` check | ~700 ms |
| Hoist the front-cache lookup to the caller so the key is built once per unique run, not once per call | ~500 ms |
| Compute `lang` once per element subtree and inherit it into `Style` instead of walking ancestors per text node | ~480 ms |
| Build the declaration table once per stylesheet, index by tag/class, reuse across nodes | ~380 ms |
| Share the inherited `Style` by reference, copy-on-write only declared properties | ~400 ms |

Total addressable: ~3.4 s of a 7.4 s cold render (46%).
