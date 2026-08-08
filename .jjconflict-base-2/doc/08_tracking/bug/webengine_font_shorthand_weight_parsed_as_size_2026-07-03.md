# Bug: `font:` shorthand parsed the weight as the pixel size (giant WM text)

- **Date:** 2026-07-03
- **Severity:** high (WM scene / web-engine fast lane text is unreadable —
  screen-filling letterforms)
- **Area:** CSS `font` shorthand parsing in the HTML layout renderer
  (`simple_web_html_layout_renderer.spl`), consumed by both the software
  painter lane and the Draw IR -> Engine2D fast lane.
- **Status:** RESOLVED 2026-07-03

## Symptom
Rendering `os.compositor.wm_scene` `standard_wm_scene(1024, 768)` through
`render_scene_to_backend` -> Metal fast lane (`scene_to_html` ->
`simple_web_layout_render_html_pixels_engine2d` -> layout -> Draw IR ->
Engine2D executor) drew the `.label` text "Simple Web WM" (and `.bar`
"workspace") as ~400-600px-tall letterforms instead of 12px text. The
`wm_gui_window_drawing` gate flagged it as `giant-glyph-pathology`
(`max_glyph_run_px=425` vs the <40 floor).

## Root cause (confirmed by probe)
The `.label` / `.bar` CSS uses the `font` shorthand: `font:600 12px system-ui`.
The shorthand parser in `compute_styles` recovered the font-size with
`parse_int(font_norm)`, which returns the FIRST integer in
`"600 12px system-ui"` — i.e. the font-**weight** `600`, not the `12px` size.
`st.font_size` was therefore `600` for every element styled with a numeric
font-weight shorthand.

Probe (`standard_wm_scene(1024,768)` -> `simple_web_layout_render_html_draw_ir`,
dumping each `DRAW_IR_COMMAND_TEXT` `computed_style` font-size):

- BEFORE: `TEXT "workspace" font-size=600`, `TEXT "Simple Web WM" font-size=600`.
- AFTER:  `TEXT "workspace" font-size=12`,  `TEXT "Simple Web WM" font-size=12`.

The 600 then flowed downstream: the software painter uses `glyph_scale(600) =
600/8 = 75` (7*75 = 525px cells), and the Engine2D executor uses `text_metrics`
`scale = 600 / glyph_height() = 600/7 = 85` (7*85 = 595px cells) — matching the
observed 400-600px glyphs. Elements that spell the weight as a keyword
(`font:bold 12px ...`) or that set `font-size:` directly were never affected;
that is why the crossengine software-painter fixtures rendered correctly and the
defect only appeared in WM chrome (`font:600 12px`).

## Not the Draw IR executor
`draw_ir_adv.spl` / `text_metrics` were NOT at fault. `Engine2D.draw_text`
already converts a pixel size to an integer glyph-cell scale
(`font_size / glyph_height()`), consistent with the software painter's
`glyph_scale(fs) = fs/8`; for the real 12px size both lanes resolve scale 1 ->
7px glyphs. No executor change was needed (or made). The bug was purely the
poisoned upstream computed font-size.

## Fix
`simple_web_html_layout_renderer.spl`: new helper `parse_font_shorthand_size_px`
(placed next to `parse_int_range`) reads the pixel size out of a normalized
`font` shorthand by locating the `px` unit and parsing the digit run
immediately in front of it, falling back to the first integer only when no `px`
length is present. The `font` shorthand branch in `compute_styles` now calls it
instead of `parse_int(font_norm)`. Keyword-weight and bare `font-size:` paths
are unchanged.

This re-lands the fix originally described in
`simple_web_widget_css_divergence_vs_chromium_2026-07-03.md` (Addendum 3) whose
renderer hunk was lost in a torn commit (`70cd415c55` carried only the doc +
`widget_store_ops.spl`).

## Verification
- Probe (above): WM-scene Draw IR TEXT font-size 600 -> 12 for the shorthand
  labels; the icon glyph "S" (`font-size:10px` directly) stayed 10.
- Render: `render_scene_to_backend(standard_wm_scene(1024,768))` fast lane,
  captured to `build/wm_textsize_fix/wm_scene_css.ppm/.png` — `max_glyph_run_px`
  drops from ~425 to the small-glyph range (label readable at ~7px).
- Gates: `check-engine2d-nomirror-fast-render-evidence.shs` (native-fast-bitexact),
  `check-engine2d-cpu-metal-parity-evidence.shs` (cpu-metal-bitexact), and the
  node bitmap lane `check-simple-web-engine2d-js-bitmap-evidence.shs` (mismatch 0)
  are unaffected — none exercise the `font:` shorthand, and the executor text
  path was not touched.

## Note: blue WM desktop is correct
The `.desktop` CSS is `background:#0f172a` with a `::before` multi-stop
`radial-gradient` accent (blue `rgba(37,99,235,.28)` + teal). The accent-blue
desktop in a correct capture is the newly-working multi-layer gradient, not a
regression; the old flat navy `0xFF0F172A` was the themed direct-rect fallback
used only above the CSS pixel cap when Metal was unavailable. No change.
