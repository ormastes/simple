# The style cascade re-parses declaration text per node: 86% of the cold document pipeline (2026-09-12)

Status: **ATTRIBUTION CORRECTED AND PARTLY FIXED (2026-09-12).** The loop named
below is real but is NOT the cost centre: level-gated counters over the same page
measure the whole author cascade at 1,029 ms and `apply_decls`' full-probe body
at **165 ms** of a 30,041 ms style stage, against **26,887 ms** in per-`#text`
font metric resolution. See the correction section at the bottom and
`doc/10_metrics/ui/web_style_cascade_after_memo_macos_2026-09-12.md`.
Platform: macOS 25.5.0 / Apple M4, `SIMPLE_EXECUTION_MODE=interpreter`.
Measured: `doc/10_metrics/ui/web_catalog_cold_render_profile_macos_2026-09-12.md`.

## Measurement

`examples/06_io/ui/web_catalog/css-layout.html` (40,960 bytes, **908 DOM nodes**)
at 900x760 on `cpu_simd`, `SIMPLE_WEB_PHASE_TRACE=1`, one cold render:

| stage | ms | share of document pipeline |
|---|---|---|
| HTML parse | 611 | 2% |
| **style cascade** | **25,229** | **86%** |
| layout | 651 | 2% |
| Draw IR build | 2,959 | 10% |
| pipeline total | 29,451 | 100% |

27.8 ms of style cascade per node, against 0.67 ms of parse per node. The cold
frame total was 263,636 ms; raster is the other 88.8% and is a separate lane.

## The loop

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:2987`
— the per-node candidate walk that accumulates one node's specificity-sorted
normal declarations into a single string, then calls `apply_decls` once per node
(`:2911` for the presentational pass, and the accumulated call below it).

The repo already knows the cost centre and says so in its own comments at
`:2965-2969`: `apply_decls` "unpacks/repacks the ~176-field Style struct" and is
"70-90% of per-node cost". What the comments do not say is that the accumulated
declaration TEXT is re-parsed from scratch for every node, including the many
nodes on a real page whose accumulated text is byte-identical because they share
a class. Nothing memoizes that.

Second leaf, same stage: `selector_group_matches_node_parts` (defined `:2211`,
called `:2944`). It is already bucketed by `style_rule_candidates` (`:2929`), so
it walks candidates-per-node rather than the whole rule set — which is why it is
the smaller half of the 25,229 ms.

## Why not fixed here

The obvious shape is a memo keyed on the accumulated declaration string. It does
not work as stated: `apply_decls` folds that text into a style that ALREADY
carries values inherited from the parent, so two nodes with identical
declaration text but different inherited bases must not share a result. A
correct memo key is (declaration text, the inherited fields the declarations can
read — `em_base` at minimum, and every `inherit`/relative-unit path). That is a
change to the style engine materially larger than the 80-line budget this lane
was given, and getting it wrong silently mis-styles a page rather than failing,
so it is filed rather than attempted.

Cheaper partial that was NOT attempted either, recorded so the next lane does not
have to rediscover it: the presentational-attribute `apply_decls` at `:2911`
takes `pres_decls`, which for most nodes is empty — a length check before the
call would skip a ~176-field unpack/repack for every node with no presentational
attributes. That one IS small, but it was not measured separately here, so the
saving is unquantified and it is not claimed.

## Correction and what actually landed (2026-09-12)

The "27.8 ms of style cascade per node" figure is a stage total divided by node
count; it was never an attribution, and reading it as one pointed two rounds of
work at the wrong leaf. Direct counters (`SIMPLE_WEB_STYLE_COUNTERS=1`, printed
as `[web-phase] style_counters` / `[web-phase] font_measure`, both level-gated
and default off) give the split on css-layout.html at 900x760, untruncated (no
`budget-break` in the log):

| leaf | calls | ms | share |
|---|---|---|---|
| per-`#text` font metric resolution | 146 | 26,887 | 90% |
| ... `measure_text_advances` inside it | 146 (2,601 chars) | 24,141 | 80% |
| author cascade total | — | 1,029 | 3% |
| `decl_table_build` | 2,190 | 461 | 1.5% |
| `selector_group_matches_node_parts` | 1,045 | 283 | 0.9% |
| `apply_decls` full-probe body | 44 | 165 | 0.5% |

Root cause of the real hotspot: the module-level ASCII glyph-advance cache in
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` held exactly ONE
`(face identity, font_size)` pair and reset its 95-entry table whenever either
changed. A page that mixes heading/body/code sizes interleaves those text nodes,
so the single slot thrashed and nearly every character paid the
SFFI-dylib-without-blob backend's full pixel rasterize just to read `.advance` —
9.3 ms per character.

Landed here:

1. **Advance cache holds 8 `(identity, size)` buckets** instead of one
   (`font_renderer.spl`). 24,141 ms -> 5,346 ms for the same 2,601 characters.
   32 buckets was measured and made no difference, so 8 is kept.
2. **Author-cascade memo** keyed on `(parent inherited identity, tag, em_base,
   writing mode, presentational decls, accumulated decls)`, with field-for-field
   copy in and out so a hit never aliases a cached `Style`
   (`simple_web_html_layout_renderer_core.spl`, `_style.spl`). 96% hit rate; it
   removes the cascade cost the record predicted, which turned out to be small.
   The parent identity in the key is load-bearing and is the sabotage target of
   `test/unit/browser_engine/style_cascade_memo_spec.spl`.
3. **Font-metric front memo** on the full argument tuple, ahead of the
   classification/shaping work whose existing identity-keyed cache is reachable
   only when a language-selected asset exists. Draw-IR compose 3,439 -> 233 ms.
4. **Presence set over the declaration table** so an absent-property probe is
   O(1) instead of a backwards scan of the merged table.
5. **Two always-on "default off" probes gated**: `_WM_TRACE` was hardcoded
   `true` (4 prints per font resolution) and `SIMPLE_TRACE_FONT_STYLE` was tested
   with `!= nil`, which `env_get` never returns (up to 7 prints per node).
6. **Metadata text is not measured**: a `#text` child of `style`/`script`/
   `title`/`head`/`meta`/`link`/`base`/`template` is never painted.
   `noscript` is deliberately excluded — this engine runs no scripts, so its
   content renders.

Net on css-layout.html: style 29,379 -> 11,591 ms (2.5x), pipeline to
compose_shaping 34,232 -> 13,722 ms. All EIGHT shared catalog pages render
byte-identical before/after (mismatch=0 each), so every change above is
pixel-neutral.

**Still open — the honest remainder.** The target was style <= 2,500 ms and this
does not reach it. `measure_text_advances` is still 5,346 ms for 2,601 characters
(2.05 ms/char) with a warm advance cache. The two named candidates, neither
attempted: `horizontal_kern` runs once per character PAIR and has no cache at
all, and the dylib-without-selected-blob backend still has no metrics-only entry
point, so a cold character costs a full pixel rasterize. Both live in
`font_renderer.spl`.

