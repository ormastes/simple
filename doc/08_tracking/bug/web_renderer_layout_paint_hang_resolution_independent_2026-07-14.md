# Perf: pure-Simple web renderer hangs in compute_styles, independent of pixel count

- **Date:** 2026-07-14
- **Severity:** high (blocks any real-HTML-page PPM evidence/showcase render)
- **Area:** src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl (compute_styles)
  + src/lib/nogc_sync_mut/text_layout/font_renderer.spl (resolve_font_metrics_with_language)

## Symptom
Rendering `examples/06_io/ui/browser_common_elements_showcase.html` (78 lines,
4.8KB, 149 parsed nodes) through the fresh seed hangs past 120-1100s even at
**20x15 = 300 px** — i.e. the previously-suspected "~70 px/s" rate is a red
herring; wall time does not scale with pixel count at all.

## Trace evidence
Using `simple_web_layout_render_html_software_pixels_traced` (existing
per-stage tracer) at 20x15:
```
[layout-trace] parse_html_ms=36 nodes=149
[layout-trace] extract_css_ms=7
```
No further `[layout-trace]` line (`compute_styles_ms`, `layout_ms`, `paint_ms`)
ever printed after 600s+ wall time. So parse (36ms) and CSS extraction (7ms)
are fine; the hang is inside `compute_styles` (simple_web_html_layout_renderer.spl:5744),
before layout or paint ever run. Confirmed resolution-independent: 320x240 and
20x15 both fail to complete within their budgets.

## Suspect
`compute_styles` calls, per `#text` node (line ~5797):
```
resolve_font_metrics_with_language(st.font_family, metric_text, st.font_size, ...)
```
which (font_renderer.spl:1021) constructs `FontRenderer.browser_default_for_family(family)`
(line ~1045) **before** its own cache lookup at line ~1049-1053. The early
cache check at line ~1035 only fires when `selected_font_asset_for_language_category`
returns a non-nil candidate with a non-empty identity — the common case (plain
Latin text, generic family names as in this showcase page) skips it, so
`browser_default_for_family` always runs first. That call constructs a brand
new `FontRenderer.new()` and, via `try_load_runtime_ttf`, iterates
`browser_font_dylib_candidates()` doing dlopen + TTF file load/parse from
disk (`FontRasterizer.load`) — a full font+dylib load **unconditionally, once
per #text node**, with no reuse across nodes. The showcase page has dozens of
text nodes (headings, paragraphs, labels, table cells, nav links, etc.); at
interpreter FFI speed each dlopen/font-parse round trip is plausibly seconds,
so total time is O(text_node_count) independent of width/height — matching
the observed hang.

## Fix direction
1. Hoist the cache check in `resolve_font_metrics_with_language` above the
   `browser_default_for_family` call (or make `browser_default_for_family`
   itself check a process-level font-renderer cache keyed by resolved family
   before constructing/loading), so repeat text nodes with the same family
   reuse one loaded `FontRenderer`/dylib handle instead of reloading per node.
2. Alternatively memoize `FontRenderer.browser_default_for_family` results in
   a module-level dict keyed by `resolved_family`, invalidated the same way
   `_try_install_ttf` already invalidates the per-renderer glyph cache.

## Update 2026-07-14: font-default caching TRIED, hang PERSISTS — suspect refined
The per-family font-renderer memoization above (fix direction #2) was
implemented and verified safe (no `font_metrics_spec`/`font_renderer_spec`
regression). Once the separate `.split(...)` seed-resolution crash that had been
masking this path was worked around (see
`web_font_provider_split_nested_call_resolution_2026-07-14`), the memoized build
was measured end-to-end at 20x15: **`compute_styles` STILL does not complete
within 420s.** So caching `browser_default_for_family` is NOT the dominant cost —
the original suspect was incomplete. The memoization was reverted (unproven
benefit, adds shared mutable state to a peer-active file); only the split
crash-fix was kept.

## Update 2026-07-14 (2): NOT a perf hang — a cascade of seed-interpreter-unsupported constructs
Per-node `[TRACE-TMP]` markers inside `compute_styles` settled it. Setup
(`build_rule_buckets`/`build_selector_context`/`build_rule_specificities`) is
instant; nodes 0-4 (#root/html/body/header/strong) process in <1ms each; then
node 5 (the first `#text`) hits, in order, hard SEED-INTERPRETER errors — not a
slow loop:
1. `method 'split' not found on value of type str in nested call context`
   (fixed: `font_provider.spl:82`, `font_renderer.spl` `_resolved_font_language`).
2. After that fix: `unsupported path call: ["FontRenderConfig", "default_for_size"]`
   — the seed interpreter cannot lower the static path call
   `FontRenderConfig.default_for_size(font_size)` (6 sites in font_renderer.spl:
   74, 788, 882, 918, 1001, 1256, several chained `.identity()`).
3. Also present throughout: `HIR lowering error: Unknown variable: unit while
   lowering _sfnt_utf16be_text` (JIT→interpreter fallback).

CONCLUSION: the earlier "hang" was the interpreter grinding on this cascade, not
an O(n) font-load or O(nodes×rules) selector cost. The pure-Simple web renderer
requires the COMPILED lane; the SEED interpreter has multiple unsupported-construct
gaps in the font/text path (static path calls, erased-receiver method resolution,
`_sfnt` HIR lowering). The deployed compiled `bin/simple` — which handles these —
is separately blocked by the `rt_cli_arg_count` unknown-extern regression. So a
web-showcase PPM is TOOLCHAIN-blocked on BOTH lanes, not a renderer-logic defect.

Fix path (either unblocks the web showcase):
- Seed: add interpreter support for static path calls (`Type.static_method()`)
  + erased-receiver builtin method resolution, and lower `_sfnt_utf16be_text`.
- OR redeploy Stage-4 `bin/simple` past the `rt_cli_arg_count` regression, then
  render via the compiled lane where these constructs already work.
