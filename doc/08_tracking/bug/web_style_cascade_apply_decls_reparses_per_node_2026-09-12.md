# The style cascade re-parses declaration text per node: 86% of the cold document pipeline (2026-09-12)

Status: OPEN, filed with the loop named. Not fixed here — see "Why not fixed".
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
