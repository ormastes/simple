# Browser Engine (Web Layout Renderer) Layer Expert

## Role

Own layer-specific process knowledge for the pure-Simple Web layout/paint engine
under `src/lib/gc_async_mut/gpu/browser_engine/`: the HTML->CSS->layout->pixels
software renderer that both the WM compositor lanes and the cross-engine widget
gates funnel through on Metal-capable hosts. Public contract: given HTML + width
+ height, produce an ARGB `[u32]` framebuffer that (a) matches pinned node
bitmap scenes byte-for-byte and (b) approximates real Chromium for themed glass
CSS.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Layer Links

- Source (owned):
  [src/lib/gc_async_mut/gpu/browser_engine/](../../../../src/lib/gc_async_mut/gpu/browser_engine/)
  - `simple_web_html_layout_renderer.spl` (~8.2k lines) — the whole pipeline.
  - `simple_web_renderer.spl` — engine2d/Metal presentation shim
    (`simple_web_render_html_to_pixels_with_engine2d_backend`,
    `simple_web_resolved_engine2d_backend_name`).
  - Browser text uses the shared Draw IR → Engine2D font-renderer path; do not add a private atlas compositor.
- Consuming feature experts:
  - [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)
    (cross-engine widget parity gate).
  - [wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
    (giant-glyph regression gate; consumer, not owner).
  - [rendering_inside_rendering](../../feature_expert/rendering_inside_rendering/skill.md)
    (iframe embedding is implemented INSIDE `simple_web_html_layout_renderer.spl`:
    replaced element, srcdoc, `space=separate|shared`, `WEB_IFRAME_DEPTH_CAP=3`).
- Related layer: [os_compositor](../os_compositor/skill.md).

## Public Contract / Key Entry Points

- `pub fn simple_web_layout_render_html_software_pixels(html, width, height) -> [u32]`
  (line ~8120): parse -> extract_css -> compute_styles -> layout -> `paint`.
  `fb` base is `argb(245,245,245)` in legacy widget_mode else white(255).
- `pub fn simple_web_layout_uses_legacy_widget_chrome(html) -> bool` = html
  contains `widget-panel` AND NOT `<style` — the fixtures embed `<style>`, so
  they use the REAL layout path (widget_mode = false), not the hand-drawn stub.
- `compute_styles` -> `Style` struct (one giant record; every new visual
  property needs a field added to BOTH the default constructor and the final
  builder `Style(...)` at line ~3555 — three call sites near lines 1684, 1688,
  3555 must stay field-consistent or it won't compile).
- Paint order in `paint` (line ~7528): per node, back-to-front: shadow
  (`fb_style_rounded_rect_opacity_clip` at box_shadow offset — HARD, no blur) ->
  background (`fb_style_background_opacity_clip`) -> border -> outline; then
  relative/absolute/positive-z passes repeat the same block.
- Gradient painting: `fb_style_background_opacity_clip` +
  `mix_color_vertical_centered` — VERTICAL linear only (varies with row);
  `parse_linear_gradient_color(raw, 0|1)` picks the first/last color of the
  first `linear-gradient(` layer; `parse_background_stack_base_color` picks the
  trailing plain-color layer. NO radial-gradient primitive, NO shadow blur, NO
  backdrop-filter compositing exist yet — these are the documented residuals.

## Known Constraints / Verification

- **Bit-exact pinned lane:** `JS_RENDER_RUNTIME=node sh
  scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`
  (`mismatch_count=0`) is the non-negotiable regression guard. Also
  `check-engine2d-cpu-metal-parity-evidence.shs` and
  `check-engine2d-nomirror-fast-render-evidence.shs`. New visual features must
  be additive branches gated on properties absent from the pinned scenes
  (radial-gradient / backdrop-filter) to be safe by construction.
- **Interpreter render cost — the O(n^2) CSS-parse blocker is FIXED (2026-07-03).**
  Root cause: `rt_string_char_at`/interp `char_at` is O(index) (`chars().nth`),
  and interp `substring` materializes `chars().collect()` of the WHOLE string per
  call — so `find_from` (a char_at scan loop) and `css_matching_close` were O(n^2)
  over the ~290 KB embedded sheet, and the nested `count_css_rules`/`extract_css`
  find+match_close pattern traversed the sheet ~85x (measured 106 s just to count
  rules). Fixes, all in `simple_web_html_layout_renderer.spl`, node-lane bit-exact
  preserved (mismatch_count=0):
  - `find_from` now uses native `index_of` + one `substring(pos,len)` offset
    (O(n) per call; the sheet is ASCII == byte==char, which the whole file already
    assumes).
  - CSS structural scanning converted to a one-time `css.bytes()` array with O(1)
    indexed byte helpers (`css_bytes_find`/`_match_close`/`_first_non_ws`/
    `_trimmed_eq`); `count_css_rules` + `extract_css` are now a SINGLE linear
    brace-depth pass (emit at each rule's closing brace, document order preserved
    for cascade parity). `css_matching_close` deleted.
  - Result on `gui/debug/simple`: window 320x200 render ~40 min -> ~85 s (28x).
    Per-stage: extract_css 275 s -> ~58 s, count 106 s -> 1.4 s. On self-hosted
    `bin/simple` (what the gates use) extract_css is ~3x the seed (~168 s); a
    window+taskbar gate run is ~355 s isolated, fits the 600 s per-render timeout
    when the host is NOT contended by other agents' renders.
  - Remaining seed hotspots if more is needed: extract_css per-rule `substring`
    (~11 s; could build sel/decl from the byte slice), `_css_collect_custom_props`
    (still a find+match_close scan, ~6 s), paint (~14 s), compute_styles (~12 s).
    Never pass the big byte array into a hot helper WITHOUT confirming it stays
    cheap — array-param is COW-cheap here (verified 1770 calls = 21 ms), the
    slowness was iteration count, not copying.
- **Interpreter codegen gotchas seen in this file:** chained methods break (use
  intermediate `var`); `obj.field.push()` on an array element doesn't persist
  (flat arena of nodes keyed by parent index is used); `text.index_of(needle,
  pos)` ignores `pos` (use `find_from`); a `var x = if cond: a else: b` block
  binding can be treated as const at runtime and crash on later reassign
  (the chromed-scene flex-stretch path hits this ~line 7012/7063).
- **Concurrent editing:** multiple agent sessions edit this file; back up each
  edit and re-verify content after any pause.

## Update Rule

When this layer's public contract, source ownership, tests, architecture, or
verification requirements change, update this skill with the new links and
handoff notes before committing.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
