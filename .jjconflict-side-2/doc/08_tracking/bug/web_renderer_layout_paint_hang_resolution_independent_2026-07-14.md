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

## Update 2026-07-14 (3): FINAL root cause — 17MB CJK font parsed in the interpreter
After the `FontRenderConfig.default_for_size` path call was worked around too
(free function `font_render_config_default_for_size`, font_types.spl +
font_renderer.spl 6 sites), instrumentation inside
`_resolve_font_metrics_with_language_config` pinned the hang EXACTLY: the first
`#text` node prints `[TRACE-TMP] resolve: before browser_default_for_family
family=Noto Sans SC` and never returns. The default sans family resolves to
**Noto Sans SC**, whose first existing candidate on this host is
`assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf` = **17 MB** CJK
variable font (Liberation Sans, the small Latin fallback, is not installed).
Loading+parsing a 17MB font runs in the INTERPRETER because the JIT cannot lower
the sfnt name-table parser (`Unknown variable: unit while lowering
_sfnt_utf16be_text`), so what looked like a "compute_styles hang" is really a
single 17MB font parse at interpreter speed on the first text node.

So the web-showcase PPM is blocked by the INTERSECTION of: (a) a 17MB default
font, (b) a JIT HIR-lowering gap that forces slow interpretation of the font
parser, and (c) the deployed-binary `rt_cli_arg_count` regression that rules out
the compiled lane. Fixed in source this session: the two `.split()` crashes and
the `FontRenderConfig.default_for_size` path call — the render now progresses
through style resolution and only stalls on the raw 17MB font parse. Remaining
unblock paths (unchanged): fix the `_sfnt_utf16be_text` JIT lowering so the font
parser compiles, OR redeploy Stage-4, OR ship a small Latin default font ahead
of the CJK candidate for Latin-script content.

## Update 2026-07-14 (4): _sfnt `unit` seed-crash fixed; font-selection is NOT a viable unblock
Pushed the smaller-font hypothesis to ground truth. Two findings:
1. **Real seed-crash fixed:** `_sfnt_utf16be_text` (sfnt.spl) used `val unit =
   units[index]`; the seed reports `variable 'unit' not found` /
   `Unknown variable: unit while lowering _sfnt_utf16be_text` — `unit` collides
   with the unit type in the seed's analyzer. Renamed to `code_unit` (pure,
   semantics-identical). This unblocked sfnt name-table UTF-16 parsing on the
   seed (the render progressed past it after the rename).
2. **Font selection cannot be changed to dodge the 17MB parse.** The default
   sans face is `Noto Sans SC` for ALL languages incl. Latin — this is BY DESIGN
   (universal Latin+Cyrillic+CJK sans face) and is LOCKED by acceptance tests:
   `shared_font_shaping_acceptance_spec.spl:59` and
   `shared_font_manifest_spec.spl:409/444` assert `Noto Sans SC` as the sans
   witness for en/es/fr/pt/ru/id. Substituting Nunito (0.3MB) renders faster but
   REGRESSES those contracts, so it was reverted.

NET: after fixing the `unit` crash, the render still cannot complete a full page
under the interpreter in practical time — even a 0.3MB font left a 20x15 render
grinding 6+ min (glyph rasterization + layout + paint per node at interpreter
speed). Confirms the compiled-lane requirement from every angle. Source crashes
fixed this session (split x2, FontRenderConfig path call, `unit`): the web font
path no longer CRASHES on the seed — it is purely throughput-bound now. Only real
unblock: fix `_sfnt_utf16be_text` JIT lowering, or redeploy Stage-4 past `rt_cli_arg_count`.

## Update 2026-07-14 (5): WEB RENDERER VERIFIED WORKING on common HTML/CSS (text-glyphs font-gated only)
Isolated the font parse from the render and got REAL PPM evidence. Method:
temporarily move the 17MB NotoSansSC aside, confirm the render COMPLETES in ~20s
(proving the font parse was 100% of the cost); then render a common-HTML/CSS page
through the REAL layout engine (`simple_web_layout_render_html_pixels_engine2d`,
reached via text tags `<h1>/<p>`) with EMPTY text (no glyph shaping, no font parse).

RESULT — `simple_web_render_html_to_pixels_with_engine2d_backend(html, W, H, "software")`
on a page with class-selector CSS (body bg + 5 colored blocks + a border) produced,
at BOTH 640x480 and 1280x720, a fully-painted frame with **8 distinct colors, every
one matching the source CSS at the correct pixel counts**: body `#EEF2FF`, blocks
`#173B7A`/`#4F46E5`/`#047857`/`#FBBF24`/`#DC2626` (each 44800px = 640x70), border
`#312E81` (8520px). Verified with a P6 distinct-color analyzer.

CONCLUSION (supersedes the "blocked" framing): the pure-Simple web engine's
parse -> CSS -> layout -> box-model -> paint pipeline WORKS and renders common
HTML/CSS (class/id selectors, backgrounds, borders, block layout, colors) to real
pixels. The ONLY remaining gap for the full text-heavy showcase page is TEXT GLYPH
rendering, which requires shaping the 17MB Noto Sans SC universal face — parse-gated
under the interpreter. Notes: (a) inline-style pages without text tags hit a
simplified HEURISTIC renderer (bg + first block only) — use real text tags for the
full engine; (b) a wrong-identity small font makes text shaping fail and collapses
the text-heavy layout to blank. Evidence PPMs:
scratchpad/verify/web2/{realeng_640,web_css_1280x720}.ppm.

## Update 2026-07-14 (6): CONFIRMED — real text showcase PPM is impossible in the interpreter (single 17MB parse > 39 min)
Applied the font-default cache (perf commit `4aa46ab4`: family->FontRenderer memo
so the 17MB Noto Sans SC loads ONCE per family, not per #text node) and rendered the
ACTUAL `browser_common_elements_showcase.html` (real text, real font) at 320x240 with
a 2400s budget. Result: the process ran **39+ minutes at 100% CPU and never produced a
PPM** — the SINGLE 17MB font parse alone exceeds the budget. The cache correctly
eliminates the per-node re-parse (confirmed: it's one load now, not 50), but one 17MB
sfnt parse in the pure interpreter is itself a 40-min operation. The JIT cannot
accelerate it: lowering the font path hits multiple gaps — `_sfnt_utf16be_text`
(fixed the `unit` crash but still can't JIT-lower), `CastElse` on `value+0.5 as i64`,
and `_set_u16_be` mut-capability — so the whole parse runs interpreted.

FINAL: the actual text-heavy showcase page CANNOT be rendered to a PPM in this
environment. It is not a wait-longer situation — the single font parse is
throughput-bound at ~40 min with no JIT acceleration. Confirmed unblock paths (only):
(1) fix the seed's JIT HIR lowering for the sfnt parser (`_sfnt_utf16be_text` +
`CastElse` + `_set_u16_be`) so the font path COMPILES, or (2) redeploy Stage-4 so the
compiled `bin/simple` (which handles all this) runs the showcase. The CSS/layout/paint
engine itself is PROVEN working (update 5); only the 17MB-font glyph path is the wall.

## Update 2026-07-14 (7): font-load cost fully characterized — sha256 fixed native, sfnt validation is the rest
Instrumented the font load piece by piece (17MB NotoSansSC blob, interpreter):
- `file_read_bytes` (17MB): **62ms** — fast, not a factor.
- `sha256_u8_hex(blob)`: was multi-minute interpreted — **FIXED** by routing to the
  native `rt_file_hash_sha256(path)` (verified byte-identical digest a3041811... ==
  registry). Removed one large interpreted cost.
- REMAINING (each interpreted, JIT can't compile the sfnt module):
  `font_runtime_ttf_default_supported` = **78s**, `validate_glyf_font_instance` =
  **199s**, `sfnt_manifest_tables_match` = **58s** (+ `sfnt_manifest_names_match`,
  untimed) — >5.6 min of pure-Simple sfnt validation per font load. The many
  read_u16_be/read_u32_be calls over the 17MB font compound into minutes because
  the JIT defers the whole sfnt module to the interpreter (lowering gaps: `CastElse`
  on `value+0.5 as i64`, `_set_u16_be` mut-capability, `_sfnt_utf16be_text`).

DEFINITIVE ROOT CAUSE: the 17MB-font validation runs entirely in the tree-walking
interpreter because the JIT cannot lower the sfnt/font module. Real unblock: make
the sfnt module JIT-lowerable (fix those three gaps), OR move sfnt validation native
(as done for sha256), OR redeploy compiled Stage-4 bin/simple. The web layout/paint
engine itself is proven working (update 5); this validation cost is the only wall
for the actual text-heavy showcase page.

## Update 2026-07-14 (8): even a 66s font load can't rescue the real render — per-node paint is also interpreter-bound
Tested short-circuiting the redundant sfnt re-validation on sha256 match (a
sha256-verified managed asset is byte-identical to the curated registry entry, so
validate_glyf_font_instance/tables_match/names_match + font_runtime_ttf_default_supported
are provably redundant). Measured effect: the NotoSansSC load dropped from >6 min
(timeout) to **66 seconds**. But rendering the ACTUAL text-heavy
browser_common_elements_showcase.html at 320x240 with the fast load STILL ran the
full **25-minute budget without producing a PPM** — after the font is loaded once
(66s, cached), the per-#text-node cost (measure_text_advances glyph metrics +
layout + paint, all interpreted because the JIT defers the module) is itself >20
min for the ~50-node page.

The short-circuit was NOT landed: it changes font-validation semantics, would break
the source-structure assertions in `test/01_unit/lib/engine/font_ffi_spec.spl`, and
— decisively — does not unblock the render anyway. Only the clean, committed native
sha256 fix (`rt_file_hash_sha256`) was kept.

ABSOLUTE FINAL: the actual text-heavy showcase page cannot be rendered to a PPM in
the interpreter. The cost is layered — sha256 (fixed native), sfnt validation
(~5.6 min, short-circuitable), AND per-node glyph-measure/layout/paint (>20 min) —
every layer interpreter-bound because the JIT cannot lower the sfnt/font module
(`CastElse`/`_set_u16_be`/`_sfnt_utf16be_text`). The ONE real unblock is a fast
lane: fix those JIT lowering gaps, or redeploy the compiled Stage-4 `bin/simple`.
The web layout/paint engine correctness is separately PROVEN (update 5, 8-color PPM).

## Update 2026-07-14 (9): DEFINITIVE CEILING — the font/render path cannot be JIT-compiled via .spl changes
Fixed two JIT construct gaps this session (`_sfnt_utf16be_text` `unit` reserved word;
`_round_glyf_metric` CastElse in sfnt_glyf) and re-measured the validations: STILL
~105s/142s/58s — the JIT now defers for a DEEPER reason: `unresolved external symbol
'rt_dir_exists' would NULL-jump in JIT; deferring to interpreter`, plus the
`_set_u16_be` mut-capability gap. These are seed-level JIT limitations (unresolved
externs, mut-capability, construct gaps across sfnt/sfnt_glyf/font_renderer/
font_registry/web-layout modules), not single constructs a rewrite can clear.

ABSOLUTE FINAL: the actual text-heavy showcase PPM is unreachable by any pure-Simple
change here. The web layout/paint engine is proven correct (update 5, 8-color PPM).
Everything reducible in Simple was reduced (7 fixes: split x2, FontRenderConfig, unit,
font cache, native sha256, glyf CastElse). The only remaining unblock is seed-compiler
work — fix the JIT to compile the font/render modules OR redeploy compiled Stage-4
bin/simple — both bootstrap-scoped, outside a safe pure-Simple drive-by.
