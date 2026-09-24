# Web document pipeline profile — macOS, 2026-09-12

Interpreter: `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39368072 1789171430`), `SIMPLE_GPU_BACKEND=cpu_simd`,
viewport 900x760, 600 s timeout, one render per page (cold).
Instrument: the level-gated counters from PR #551/#559/#566
(`SIMPLE_WEB_PHASE_TRACE=1 SIMPLE_WEB_STYLE_COUNTERS=1`) plus one temporary
layout counter, since reverted — `git diff --stat -- src/lib` is empty.

## Stage boundaries

| page | nodes | parse | style | layout | DrawIR/compose | total |
|---|---|---|---|---|---|---|
| `css-layout.html` | 908 | 648 ms | **5791 ms (78%)** | 762 ms | 211 ms | 7412 ms |
| `overview.html` | 43 | 45 ms | **867 ms (87%)** | 21 ms | 67 ms | 1000 ms |

Style dominates both, and it is not the cascade (935 ms of 5791; 79 ms of 867).

## Top 10 by self cost (css-layout.html / overview.html)

| # | leaf | ms (css-layout / overview) | calls | file:line | class |
|---|---|---|---|---|---|
| 1 | `resolve_font_metrics_with_language` (style-time font resolve) | **2940 / 713** | 146 / 15 | `simple_web_html_layout_renderer_core.spl:3295` → `font_renderer.spl:2964` | per-call fixed cost, no memo |
| 2 | `renderer.measure_text_advances` — **nested inside #1, not additive** | 490 / 237 | 146 / 15 | `font_renderer.spl:2919` | per-char work (2601 chars / 490 ms) |
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

Two hypotheses tested and **refuted**: face reloading per text node
(`SIMPLE_WM_TRACE=1` gives `from_cache=true` on 144 of 146 resolves), and
redundant re-layout (a temporary counter at `..._layout.spl:1346`, since
reverted, recorded 772 calls over 772 *distinct* box indices — one per box).

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
5. **Style cost scales with total text length, not node count.** 43 nodes →
   867 ms vs 908 nodes → 5791 ms (21x the nodes, 6.7x the time), while per-text-run
   cost moves the other way (47 ms on overview, 20 ms on css-layout) — it is set
   by run length, which is what defect 1 makes O(len) five times over.

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

---

# Follow-up — cold document pipeline, measured 2026-09-13 (PR `work/web-cold-pipeline-perf-2026-09-13`)

Same interpreter path, different host and a different binary, so **the numbers
below are not comparable to the table above** — only the before/after pair
within this section is. Interpreter
`/Users/ormastes/simple/build/cargo-r2/release/simple` (`stat -f '%z %m'` =
`39528776 1789199850`), `SIMPLE_EXECUTION_MODE=interpreter`, viewport 900x760,
one render per page. This host measured **14,520 ms** on `css-layout.html`
against the 7,412 ms recorded above, i.e. it is roughly **2x slower**; scale
accordingly before comparing to F22's targets.

Instrument: a scratch driver (uncommitted, `build/perfbench/pipeline_bench.spl`)
that renders all eight catalog pages to Draw IR in ONE process via
`simple_web_layout_render_html_draw_ir_result`, printing per-page pipeline ms
and an FNV-1a/32 digest over the Draw IR command stream (kind, component_id,
x/y/w/h, color, text_value, advance_widths, glyph ids/xs). Pipeline ms covers
parse + style + layout + compose — it does NOT include rasterisation.

## Per-page cold pipeline, before and after

| page | before (ms) | after (ms) | change | Draw IR digest before → after |
|---|---|---|---|---|
| `animation` | 3686 | 2102 | -43% | `ce65599f` → `ce65599f` |
| `css-layout` | 14520 | **6148** | **-58%** | `dabf5ee9` → `dabf5ee9` |
| `css-paint` | 18735 | 8676 | -54% | `fc54822c` → `fc54822c` |
| `evidence` | 422 | 182 | -57% | `115f7f9a` → `115f7f9a` |
| `forms-media` | 3392 | 1469 | -57% | `0892abbc` → `0892abbc` |
| `html` | 14235 | 4774 | -66% | `55dbad8d` → `55dbad8d` |
| `overview` | 1032 | 425 | -59% | `0dc9572b` → `0dc9572b` |
| `tab-bar` | 753 | 380 | -50% | `de129f37` → `de129f37` |
| **total** | **56,775** | **24,156** | **-57%** | 8 of 8 identical |

All eight Draw IR digests are byte-identical across the change. Every catalog
page carries a `lang=` attribute on `<html>`, so the inherited-language path is
exercised on all eight — a broken inheritance chain would have answered `und`
for every text node and moved the digests.

## Where the time actually went (`SIMPLE_WEB_STYLE_COUNTERS=1`, css-layout)

F22 attributed the 2,450 ms residual inside the font resolve by reading the
code. Measured, it was somewhere else entirely. Buckets added in this change
(`_fr_probe_add_cls/key/lookup/face/faceid/lineh`, level-gated, permanent):

| bucket | before this change | after | note |
|---|---|---|---|
| `face_ms` — `_browser_default_for_family_cached` | **6510** | **207** | 146 calls, ~44 ms each; re-parsed the in-memory OpenType blob per resolve |
| `cls_ms` — language/complex-script/category classification | 1151 | 655 | |
| `measure_ms` — `measure_text_advances` | 1974 | 1237 | |
| `key_ms` — the two full-content cache keys | 27 | 10 | F22 estimated ~900 ms for this; it is noise |
| `lookup_ms` — identity-cache lookups | 35 | 21 | the 128-entry linear scan was never the cost |
| `sec_lang_ms` — `_html_text_language` | 511 (F22 host) → 28 | 22 | |
| `table_ms` — declaration-table build | 417 (F22 host) → 57 | 37 | |

(The two "before" columns are from runs under different host contention; the
ratio within each run is what carries, not the absolute.)

**Correction to F22, stated rather than quietly dropped.** Three of its six
proposed fixes were sized from the wrong hypothesis: content hashing (~900 ms)
and front-key hoisting (~500 ms) address `key_ms`, measured at 27 ms, and the
identity cache's linear scan is 35 ms. The single dominant term — 64% of the
font-resolve bucket — was a face rebuild F22 did not list at all, because the
flat `(family, path)` cache *looks* like a cache and its own comment says the
rebuild reads "no VFS". It does not re-read the file; it re-parses the blob.

## What landed

1. **Live-face memo** (`font_renderer.spl`). The flat cache's hit path now
   returns a shared `FontRenderer` keyed by the same `cache_key`, re-checking
   `has_sffi_ttf()` on every hit so a torn-down face falls through to a real
   rebuild. `from_cache = true` is what the rebuild already returned, so no
   caller starts or stops calling `clear_ttf()`. 6510 ms → 207 ms.
2. **Dict index over the resolved-metrics ring** (`font_renderer.spl`). The
   lookup was a linear scan of up to 128 keys each embedding the full text
   content. Eviction removes the evicted key from the index before the slot is
   reused, and the lookup re-checks `keys[slot] == key`. Small win (35 → 21 ms),
   kept because it removes an O(cache) term that grows with the limit.
3. **Classifier memos** (`font_renderer.spl`). `_resolved_font_language` and
   `_resolved_font_category` are pure in one short string; the latter walked the
   whole candidate list with a `.lower()` per candidate. Reset together with the
   selected-asset registry they derive from.
4. **Top-down inherited `lang`** (`..._core.spl`). One `attr_value` parse per
   node, inheriting the parent's answer, replacing an O(depth) ancestor walk per
   text node. The `font-language-override` branch and any node whose parent
   index is not below its own still call `_html_text_language`, so the fallback
   is code, not an assumption.
5. **Declaration-table memo** (`..._foundation.spl`). `decl_table_build` is pure
   in its argument and all four call sites treat the result as read-only.

## Honest scope — not done

- **Target missed.** The goal was ≤3 s cold pipeline on `css-layout`; this lands
  at 6,148 ms. On F22's host (2x faster on the same page) that is ~3.1 s, but
  this lane did not measure that host and will not claim it.
- **Remaining hotspots, unfixed:** `sec_inherit_ms` (the whole-`Style` copy per
  node, F22 defect 4) and `parse` — both still open, both sized in the counters
  above.
- **`measure_text_advances` weight argument (F34/F36) NOT added.** There is no
  weight or variable-axis plumbing anywhere in `font_renderer.spl` — no `wght`,
  no axis setter, no synthetic-bold path; the axis lives in the font registry's
  candidate `default_axes`. A `weight` parameter that no caller could act on
  would be unused API, and one that changed advances would move the catalog
  pixels, which this lane is forbidden to do. It needs its own change with its
  own pixel budget.
- **Pixel gate:** Draw IR digests (all eight pages) are the oracle used here.
  The full `gpu_boundary_audit` rasterisation of `css-layout` costs ~11 minutes
  per page per side on this host, so it was run for `css-layout` only.
