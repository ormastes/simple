# Finding: Simple web engine diverges structurally from Chromium on widget CSS

- **Date:** 2026-07-03
- **Severity:** high for "production level" widget rendering claims
- **Area:** simple web layout renderer draw-ir/engine2d lane (widget CSS features)
- **Gate:** scripts/check/check-widget-shells-crossengine-evidence.shs (exit 1, status=divergent)

## Measured (same HTML, generate_css("light") widget docs)
| fixture | Simple<->Chrome | Simple<->Electron | Chrome<->Electron |
|---|---|---|---|
| gui window 320x200 | 50.31% | 50.69% | **99.89%** |
| taskbar 480x64 | 47.01% | 47.12% | **99.93%** |
(non-text pixel agreement; per-channel tol <=8, sRGB-normalized, no blur;
glyph pixels excluded via Chrome DOM text mask)

## Finding
The two independent real browsers agree ~99.9% — the HTML/CSS is valid and
consistently rendered. The Simple lane renders a flat fill + single top border
where Chromium renders: border-radius (rounded cards/pill), box-shadow,
linear-gradient backgrounds, accent borders, and nested panel-content boxes.
Panel band top offset 8px (Simple y22 vs Chromium y14).

## Note on lanes
The SOFTWARE painter has rounded-rect/opacity machinery
(fb_rounded_rect_opacity_clip etc.), but the draw-ir lane emits plain
boxes (draw_ir_box_with_style -> RECT) with bg color only — radius, shadow,
gradient, and border props ride along as style strings and are not painted
by the engine2d executor. Closing this = teaching the draw-ir command set +
executor the missing box decorations (or routing widget docs through the
software painter's decorated path and uploading).

## Artifacts
build/widget_shells_crossengine/{simple,chrome,electron}_{window,taskbar}.png
+ report.md (2026-07-03 run).

## Also noted (pre-existing runtime gaps, not worked around silently)
- rt_string_builder_new extern unavailable in current self-hosted runtime
  (array-backed StringBuilder fallback used).
- Reading a binary PNG via std.io_runtime.file_read crashes the interpreter
  on rt_dir_exists.

## Fix (2026-07-03, worktree)
Lane correction: the widget docs never went through the draw-ir executor —
`simple_web_engine2d_render_html_pixels` routes selector-CSS docs to the
SOFTWARE painter (`paint()` in simple_web_html_layout_renderer.spl). The
"flat fill + single top border" was painted there. Root causes, all in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:

1. `base_selector_matches` never matched `*` — the theme's
   `* { margin:0; padding:0; box-sizing:border-box }` reset silently no-oped,
   so the UA body margin 8px survived. This was the exact 8px panel band
   offset (Simple y22 vs Chromium y14). Fixed: `base == "*"` matches.
2. `simple_match` treated `:root[data-wm-*]` parts as always-true (empty base;
   attr expr rides after the pseudo colon) — every theme-variant override
   (incl. `:root[data-wm-transparency=off] .widget-panel { background:
   rgba(10,10,15,0.96) }`) applied to every doc. Also `:hover/:focus/:active/
   :disabled/:checked` matched statically. Fixed: `:root` matches only the
   html element with its attr expr evaluated; interactive-state pseudos never
   match in a static render.
3. `parse_linear_gradient_color` broke on nested parens (`rgba(...)` stops)
   and `deg` angles, so `linear-gradient(180deg, rgba(...), rgba(...)), #f5f5f5`
   fell back to parse_color_any -> opaque white. Fixed: paren-aware top-level
   split, angle-item skip, alpha-aware stops (`parse_color_alpha`), and the
   trailing color layer of a background stack now lands in `st.bg`
   (`parse_background_stack_base_color`). Gradient rows blend per-row by stop
   alpha, so `panel-title`'s alpha-only gradient composites over the parent.
4. The legacy flat widget chrome overlays in `paint()` (`fb_rect` #f5f5f5 to
   frame bottom + 1px accent line for `.widget-panel`, flat #cbd5e1 for
   `.widget-button`) stamped over the styled paint. Fixed: overlays are
   skipped when the node's computed style already paints a background
   (st.bg or gradient set); styleless legacy docs keep the old pixels.
   box-shadow now parses rgba alpha and paints alpha-blended instead of
   opaque black.

Measured after (Simple software lane, structural): window 320x200 panel band
top y15 (Chromium reference y14, was y22), rounded 20px panel corners, accent
focused borders, blended gradients, nested panel-content boxes all render;
taskbar 480x64 renders the 999px-radius pill. Spec evidence: 119 pinned
assertions green (simple_web_renderer_spec 79, engine2d_renderer 13,
css_cascade 3, css_vars 2, titlebar_nowrap 1, layout_child_index 21).
Cross-engine agreement could not be re-measured on this host (Electron not
installed; captures out of scope) — re-run
scripts/check/check-widget-shells-crossengine-evidence.shs where Chrome +
Electron are available. Note: src/app/wm_compare/
production_gui_window_taskbar_widget_shells.spl was deleted by unrelated
commit adfcb2ba45 and is restored alongside this fix.

## Remaining gaps (honest)
- box-shadow: hard-edged, alpha-blended, offset-only — no blur; Chromium's
  large soft glows (blur 20-100px) are absent, so shadow halo pixels still
  diverge.
- Multi-layer backgrounds: only the last linear-gradient layer + trailing
  color layer paint; the body's radial-gradient accent tints are not painted.
- overflow:hidden + border-radius does not round-clip children (panel-title
  corners stay square inside rounded panels).
- Draw-ir executor still paints plain RECTs (radius/shadow/gradient props
  ride along unpainted) — only affects the unused
  simple_web_layout_render_html_pixels_engine2d fast lane; no production
  caller today.
