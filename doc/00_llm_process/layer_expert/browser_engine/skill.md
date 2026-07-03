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
  - `famous_site_glyph_compositor.spl` — glyph atlas compositor (separate path).
- Consuming feature experts:
  - [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)
    (cross-engine widget parity gate).
  - [wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
    (giant-glyph regression gate; consumer, not owner).
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
- **Interpreter render cost is CSS-parse-bound** (~25-30 min for a themed
  480x64 fixture under `gui/debug/simple` on a loaded host). Not a hang; budget
  timeouts generously and batch edits.
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
