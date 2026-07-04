# Office sheet-GUI: real event dispatch exists framework-wide, but the sheet grid has no per-cell click target to hit-test against

**Date:** 2026-07-04
**Severity:** medium (blocks real mouse/keyboard click-to-select on the sheet-GUI pixel path; state-driven equivalent shipped as the honest MVP instead)
**Status:** open — diagnosis complete, feeds the OS/UI lane

## Summary

The GPU-rendering gap analysis (2026-07-01) reported ZERO event-handling
tests in the UI stack and implied the framework might be one-shot-render
only. That is **not quite right**: `common.ui.event` has a real, working
event-dispatch machine. The gap is narrower and more specific: the office
sheet grid widget has no addressable per-cell target for that machine to
hit-test against, and `office/gui.spl`'s render path never calls it at all.

## What is real (verified by reading, not assumed)

- `src/lib/common/ui/event.spl:37` `process_event(state: UIState, event:
  UIEvent) -> UIState` is a genuine state-transition dispatcher: mode
  switches, keybindings, `handle_action` for named actions
  (`focus_<id>`, `toggle_<id>`, `sort_col_<n>`, `select_<list_id>_<n>`,
  `filter_<table_id>`).
- `handle_pointer` (`event.spl:230`) hit-tests a laid-out tree at real
  `(x, y)` via `widget_dispatch_click`/`widget_dispatch_hover`
  (`common.ui.widget_hit`) and moves `state.focused_id` to whatever widget
  was hit — this is coordinate-based click routing, not a stub.
- `src/app/ui.render/html_widgets.spl:71-72` (`render_html_widget`) computes
  a real per-widget "focused" CSS class by comparing `node.id ==
  state.focused_id` on every render — reused as-is by this change (see
  below), no framework edits needed.
- `src/app/office/interactive.spl` (`run_sheet_tui_mode`) is a second,
  independent real event loop: actual termios raw-mode keystrokes drive
  cell navigation/edit/recalculation today. That loop targets a different
  backend (TUI), not the browser-engine pixel GUI path this bug is about.

## The specific gap

- `common.ui.builder.table_widget` (`builder.spl:259-288`) folds every
  sheet row into **one child text node** whose `label` prop is a single
  `"|"`-joined string (`"Widget|10|2|20"`), not one widget per cell.
- `html_widgets.spl`'s `render_html_table` (`:268-307`) splits that string
  back into plain `<td>{cell}</td>` tags with **no `id`, no
  `data-action`, no per-cell anything** — only the `<th>` gets
  `data-action="sort_col_{n}"`, and the whole table gets one
  `filter_{table_id}` action on its filter input.
- Net effect: there is no widget id per cell for `widget_dispatch_click` to
  hit, and no action name a click could produce that means "select cell
  D2." Click-to-select on today's sheet grid cannot be wired without
  changing `table_widget`/`render_html_table` — shared framework code, out
  of the office lane's owned files (`src/app/office/gui.spl`,
  `src/app/office/mod.spl`).
- Separately, `office/gui.spl`'s existing render functions
  (`office_gui_frame`, `office_gui_sheet_pixels`, etc.) never call
  `process_event`/`init_state`+loop at all — each is a single build-tree,
  build-state, render-once call. There is no live session loop anywhere in
  the office GUI pixel path today, sheet grid or otherwise.

## What shipped instead (this change)

`SheetGuiSession` + `session_select`/`session_edit` +
`sheet_gui_view_with_selection` in `src/app/office/gui.spl`: a real
session/state/edit/recalculate/re-render loop, with the input-DEVICE layer
(mouse/keyboard → `UIEvent`) stubbed — `session_select`/`session_edit` are
called directly instead of routing synthetic `UIEvent.MouseEvent`/
`KeyPress` through `process_event`. The selected cell gets a **real**
"focused" CSS class by building the grid as one `text_widget` per cell
(id `cell_<ref>`) via `row()`/`column()` panels instead of `table_widget`,
then setting `UIState.focused_id = "cell_<ref>"` directly — this reuses
`render_html_widget`'s existing focus-class mechanism unmodified, it does
not invent a new one.

## What would close this gap (for the OS/UI lane)

1. Extend `table_widget`/`render_html_table` to emit one addressable child
   per cell (id + optional `data-action="select_cell_<ref>"`), or add a
   parallel `cell_grid_widget` builder that does.
2. Add a `handle_action` case (or reuse `select_<id>_<n>` two levels deep:
   row then column) that maps a cell click action to `focused_id` the way
   `focus_<id>` already does.
3. Wire one office GUI entry point to a real loop: `init_state` →
   `process_event` per incoming `UIEvent` → re-render, instead of a single
   build-then-render call — today NOTHING in `office/gui.spl` closes that
   loop, sheet grid or otherwise.
4. Feed real OS mouse/keyboard input into `UIEvent`s (currently no office
   GUI backend does this at all; `run_sheet_tui_mode` does it for the TUI
   backend only, via termios, not via `common.ui.event`'s `UIEvent`
   variants).
