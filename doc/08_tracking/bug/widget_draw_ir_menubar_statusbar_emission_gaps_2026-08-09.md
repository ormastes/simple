# Pixel Draw-IR pipeline: statusbar text never emitted, menubar items overlapped, input placeholder dropped

- **ID:** widget_draw_ir_menubar_statusbar_emission_gaps_2026-08-09
- **Status:** FIXED 2026-08-09
- **Found by:** computer-use 3D/web/2D showcase sweep, 2026-08-09 (2D PPM and
  web HTML captures of `src/app/ui_showcase` both showed an empty statusbar
  strip and an unreadable menubar)
- **Area:** `src/lib/common/ui/widget_draw_ir.spl`, `src/lib/common/ui/builder.spl`
- **Severity:** medium — every pixel-pipeline consumer (2D/gui/web showcase
  hosts) rendered statusbars empty and menubar labels stacked on one spot

## Symptoms

1. **Statusbar rendered as an empty bar.** `statusbar()` stores its text in
   `left`/`right` props, but `widget_draw_ir._emit_widget` had no `statusbar`
   case — it fell into the generic container branch (surface rect only) and
   the props were never read.
2. **Menubar items overlapped.** `builder.menubar`/`menubar_rich` left the
   node's layout at the default (`fixed`), which gives every child the full
   bar rect; all item labels painted at the same left edge. (The TUI renderer
   lays items out itself and was unaffected.)
3. **Empty text inputs showed nothing.** The `input`/`textfield` case only
   drew the `value` prop; with no value the `placeholder` was dropped and the
   field read as a bare box (showcase probe input's "type here" invisible).

## Fixes

- `_emit_widget` gained a `statusbar` case: bar fill plus `left` text at
  x+6 and `right` text right-aligned using the measured text width (same
  probe-`command.width` pattern as the input caret).
- `_emit_widget` gained a `menubar` case: explicit bar fill (item text is
  emitted by the normal child walk).
- `builder.menubar`/`menubar_rich` now set `layout = "hbox"` so items are
  spread horizontally in the pixel pipelines.
- The `input`/`textfield` case emits the `placeholder` (in
  `theme.text_secondary`) when `value` is empty.

## Deliberately NOT changed

- The 1px default height for menubar/statusbar in `layout.get_fixed_height`
  is a spec-locked TUI character-cell contract
  (`widget_menubar_statusbar_spec.spl`, `layout_spec.spl`). Pixel hosts pin a
  real height at the call site instead (`SC_BAR_H = 22` in
  `src/app/ui_showcase/showcase_core.spl` via `with_height`).
- Panel titles (`panel(id, title, ...)`) are still not rendered by the pixel
  pipeline — tracked in
  `widget_draw_ir_panel_title_not_rendered_2026-08-09.md`.

## Verification

- `widget_menubar_statusbar_spec` 64/64, `showcase_core_spec` 13/13,
  `widget_draw_ir_theme_spec` 8/8, `widget_draw_ir_glyph_run_spec` 4/4,
  `global_menubar_spec` 5/5, TUI demo `demo_menubar_statusbar.spl` all-PASS.
- Web + 2D re-captures show a readable spread menubar, `ready` / `0 events`
  in the statusbar, and the `type here` placeholder.
- Pre-existing, unrelated reds (identical on pristine HEAD): `builder_spec`
  3 (grid/dict + default-theme), `layout_spec` 1 (grid/dict),
  `widget_coverage_spec` 2 (dialog widget), `widget_menu_tooltip_spec` 1
  (`has-submenu` class).
