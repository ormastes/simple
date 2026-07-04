# Office sheet-GUI: real event dispatch exists framework-wide, but the sheet grid has no per-cell click target to hit-test against

**Date:** 2026-07-04
**Severity:** medium (blocks real mouse/keyboard click-to-select on the sheet-GUI pixel path; state-driven equivalent shipped as the honest MVP instead)
**Status:** RESOLVED (2026-07-04) — three halves closed. `sheet_gui_view_with_
selection`'s grid was closed same-day; see "Resolution" below. `sheet_gui_
view`'s plain grid was closed next; see "Resolution part 2 (GUI polish
pass)" below. The OS-input-bridge gap (residual #4, click/key routes were
scripted, never real device input) is now closed for TERMINAL input; see
"Resolution part 3 (live keystroke loop)" below. The only remaining
residual is windowed/compositor mouse+keyboard for the browser-engine GUI
backend (a real OS window's event loop, not a terminal) — out of scope for
this office lane.

## Resolution part 3 (live keystroke loop, 2026-07-04)

Closes the terminal half of residual #4 ("Feed real OS mouse/keyboard input
into `UIEvent`s ... `run_sheet_tui_mode` does it for the TUI backend only,
via termios"): `office sheet-gui-live` now drives `SheetGuiSession` from
REAL termios keystrokes, the same input device `run_sheet_tui_mode` already
used for the separate TUI-grid backend — this is the sheet-GUI-session
backend's turn.

Shipped:
- `src/app/office/interactive.spl`: `decode_key_byte`/`KeyDecodeResult` — the
  ESC `[` A/B/C/D arrow-escape-sequence state machine `tui_apply_key` used to
  inline, extracted so both loops share ONE decoder (`tui_apply_key` was
  rebuilt on top of it, verified byte-for-byte behavior-preserving by the
  full pre-existing `interactive_spec.spl` suite staying green, 8/8,
  unmodified). `run_sheet_gui_live(sheet)` — the live loop itself: renders a
  frame via the real `office_gui_sheet_session_pixels` pixel path, reads one
  raw byte via the same `rt_stdin_read_byte`/`rt_terminal_enable_raw_mode`/
  `rt_terminal_disable_raw_mode` externs `run_sheet_tui_mode` uses, decodes
  it, and steps the session — re-rendering after every accepted key. `q` or
  Ctrl-C (byte 3, since raw mode's `cfmakeraw()` clears `ISIG` — see
  `raw_mode_extern_registry_2026-07-03.md`'s fix option 3) quits.
- `src/app/office/gui.spl`: `GuiLiveStepResult`/`run_gui_live_step(session,
  key, max_rows, max_cols, view_rows, view_cols)` — the loop's pure,
  spec-testable per-keystroke core (a live raw-mode loop can't itself be
  driven from a spec): forwards arrows/chars/enter/backspace/escape to
  `session_key` unchanged, and turns `"q"`/`"ctrl_c"`/`"eof"` into
  `GuiLiveStepResult.quit = true` with the session returned UNCHANGED (a
  quit key never drops in-progress typing).
- CLI: `simple office sheet-gui-live` (`_run_office_gui_sheet_live_command`
  in `mod.spl`).
- Non-TTY safety: `rt_terminal_enable_raw_mode()` returns `false` when stdin
  isn't a real terminal (`tcgetattr` fails on a pipe/redirect — an existing
  signal, not a new TTY-detection extern) — `run_sheet_gui_live` prints
  exactly one rendered frame plus a documented notice and returns 0 instead
  of blocking on a keystroke that will never arrive, so CI/non-interactive
  callers can exercise the entry point without hanging.
- Spec: `test/01_unit/app/office/sheet_gui_session_spec.spl`'s "live loop
  step" describe block (6 new `it`s: down-moves-selection,
  chars+enter-commits+recalculates, escape-cancels-buffer, q-quits,
  ctrl_c-quits, eof-quits) plus the full pre-existing suite (25 `it`s)
  staying green — 31/31.
- Smoke: `printf '' | timeout 30 <simple> run src/app/office/mod.spl office
  sheet-gui-live` prints one rendered frame (pixel-proof line + text_dump)
  followed by the non-TTY notice and exits 0.

Scope note: like `session_click`/`session_key` before it, this bridges REAL
OS keystrokes into the session for the TERMINAL backend only. It does not
feed input into `common.ui.event`'s `UIEvent` variants (still no framework
change needed — `session_key` was already the chosen translator, see the
"Keyboard interaction" comment block in `gui.spl`), and it does not address
a windowed/compositor GUI's mouse+keyboard event source, which remains the
one open item below.

## Resolution part 2 (GUI polish pass, 2026-07-04)

`sheet_gui_view` (the read-only, no-session grid used by the plain
`sheet-gui` CLI) no longer builds its own `table_widget` grid at all. It is
now a thin wrapper over `sheet_gui_view_with_selection` (session created via
`session_new(sheet, "")` — an empty `selected_ref` never matches a real cell
ref, so no bracket/focus ever renders), so every cell in the read-only view
is now the SAME real, addressable `text_widget` with id `cell_<ref>` that
`sheet_gui_view_with_selection`'s cells always were. The plain-table-grid
code path (item 1 of "What would close this gap" below) no longer exists in
`sheet_gui_view` at all — there was nothing left needing a shared-framework
`table_widget`/`render_html_table` change, because the office lane simply
stopped using `table_widget` for the sheet view (pivot's grid still does,
and is unaffected — pivot's use of `table_widget` was never part of this
gap).

Byte-compatibility: `sheet_gui_view`'s dump format is unchanged (verified by
the full pre-existing `sheet_gui_view_spec` suite staying green, 9/9,
unmodified) despite the internal rewrite — see gui.spl's `sheet_gui_view`
docstring for how the old "scan grid rows 1..max_rows, skip hidden, no
backfill" semantics is preserved on top of `sheet_gui_view_with_selection`'s
different (N-visible, backfilling) windowing semantics: the row count
passed down is computed as the number of visible rows already within that
exact range, which forces the delegated call to stop before it would ever
need to backfill.

Item 1 of "What would close this gap" below is therefore no longer
applicable to `sheet_gui_view` (superseded by this resolution) — the
remaining items (2-4) are unchanged and still open for whichever lane wires
a live GUI event loop / real OS input.

## Resolution (2026-07-04)

`sheet_gui_view_with_selection`'s per-cell `text_widget`s (id `cell_<ref>`)
turned out to be enough on their own: `widget_dispatch_click`
(`widget_hit.spl:80-98`) hit-tests and returns ANY widget's id under the
point — there is no `clickable` flag or registered action a widget needs; it
only does *extra* prop work for `checkbox`/`input`/`textfield` kinds. So no
framework change was required to make cells clickable. What was missing was
purely an office-lane entry point that ROUTES a pointer event through
`process_event`/`handle_pointer` instead of calling `session_select`
directly.

Shipped in `src/app/office/gui.spl`:
- `session_click(session, x, y, max_rows, max_cols, viewport_w, viewport_h)`
  — builds `sheet_gui_view_with_selection`'s tree, sends a real
  `UIEvent.Resize` (sets the hit-test viewport) then a real
  `UIEvent.MouseEvent(..., kind: "down")` through `process_event`
  (`common.ui.event`), reads the hit id back off `state.focused_id`, maps
  `cell_<ref>` back to `<ref>`, and returns a new session with that
  selection. A click that hits no `cell_` widget (empty-space miss, or a
  header/row-header widget) leaves the selection unchanged — real
  click-miss semantics from `handle_pointer`, not a stub.
- `sheet_gui_cell_rect`/`sheet_gui_cell_click_point` — compute a cell's
  laid-out rect/center point via `common.ui.layout.compute_layout`, the SAME
  layout pass `widget_hit_test` runs internally. Layout is NOT cached
  anywhere — every hit-test (and every `session_click` call) re-runs
  `compute_layout` fresh over the tree at the caller-chosen viewport, so a
  click's (x, y) is only meaningful together with the viewport it was
  computed against.

CLI: `simple office sheet-gui-click` (`_run_office_gui_sheet_click_command`
in `src/app/office/mod.spl`) scripts BEFORE (D2 selected) → compute the
point that lands on B2 → real click → prints
`office-gui-click: hit=<ref>` → AFTER dump showing `[10]` (B2) selected.

Spec: `test/01_unit/app/office/sheet_gui_session_spec.spl`'s "pointer
selection" describe block (4 new `it`s, all green, deliberate-fail probe
run) covers: click-lands-on-B2, click-outside-viewport-is-a-miss,
click-on-header-widget-is-a-miss, and click-then-edit end to end.

The one remaining item from "What would close this gap" is #1 (extend
`table_widget`/`render_html_table`, or a `cell_grid_widget`, for
`sheet_gui_view`'s plain grid) — out of scope for this pass, unchanged.

## Keyboard addendum (2026-07-04, same day)

Probe finding: `common.ui.event.process_event` DOES have a real key-dispatch
path — `UIEvent.KeyPress(key)` (`event.spl:52-53`) routes through
`handle_keypress` to per-mode handlers (`event.spl:79-138`), and there is
also a real direct-focus event, `UIEvent.FocusEvent(target_id, "focus")` ->
`handle_focus_event` (`event.spl:260-271`). So this is not a "zero key
support" framework, unlike a literal reading of the task's fallback
condition might suggest. But neither primitive fits sheet-grid keyboard
interaction without changes outside this lane's owned files:

- `handle_normal_key` (`event.spl:97-109`) only recognizes `"j"`/`"k"`
  (linear `focus_next`/`focus_prev` over `tree.all_widget_ids()` in DOM
  order) — there is no `"up"`/`"down"`/`"left"`/`"right"` key name anywhere
  in `process_event`, and no 2D row/column concept: `focus_next`/
  `focus_prev` cannot express "same column, next visible row" or "skip a
  hidden row" without knowing the grid's shape, which lives in the sheet
  lane, not the framework.
- Typed-character routing (`handle_insert_key` -> `widget_hit.spl`'s
  `widget_dispatch_key`, `widget_hit.spl:141-158`) only acts on widgets
  whose `kind` is `"input"` or `"textfield"` (a hard-coded name check);
  `sheet_gui_view_with_selection`'s per-cell widgets are `text_widget`s
  (kind `"text"`), so `widget_dispatch_key` is a silent no-op on them today.
  Making cells accept typed input through that exact path would mean
  changing `builder.spl`/`widget_hit.spl`'s kind dispatch — shared
  framework code, outside `src/app/office/gui.spl`'s owned scope, the same
  shape of gap already documented above for `table_widget`.

Unlike `session_click` (which genuinely needs `process_event`/
`handle_pointer`: there is no way to know which widget a raw `(x, y)`
point lands on without running the real hit-test over a laid-out tree),
arrow-key navigation has no such geometry dependency — the target ref is
fully determined by grid arithmetic (current ref + direction + hidden-row
skip + clamp). Routing that arithmetic through `process_event`/
`UIEvent.FocusEvent` would not reuse any framework behavior (nothing in
`process_event` participates in computing *which* ref is next); it would
just be a build-tree-and-discard-the-result detour.

Shipped in `src/app/office/gui.spl`: `session_key(session, key, max_rows,
max_cols)` — a thin session-level translator. `"up"`/`"down"`/`"left"`/
`"right"` move `selected_ref` via `_sheet_gui_move_within_bounds` (reuses
`cell_ref.spl`'s existing `offset_ref` CellRef-delta helper for the raw
arithmetic; adds only the upper-bound clamp and the hidden-row skip loop,
which have no framework equivalent) and discard any uncommitted pending
buffer. `"enter"` commits a non-empty pending buffer into `selected_ref`
via `session_edit` (recalculation runs) and clears the buffer. `"escape"`
discards the buffer without committing. `"backspace"` trims the buffer.
Any other single-character key appends to the buffer (mirrors
`widget_dispatch_key`'s own `key.len() == 1` "printable" convention, just
applied to a `text_widget` cell). `SheetGuiSession` gained a
`pending_input: text` field; `sheet_gui_view_with_selection` renders the
selected cell as `"<ref>:<buffer>"` instead of the `"[...]"` bracket form
while a buffer is pending.

CLI: `simple office sheet-gui-key` (`_run_office_gui_sheet_key_command` in
`src/app/office/mod.spl`) scripts BEFORE (B2 selected) → `down` (B3) →
`"9"`, `"9"` (buffer accumulates) → `enter` (commits, recalculates) → AFTER
showing B3=99, D3 (`=B3*C3`) = 297, D5 (`=SUM(D2:D3)`) = 317, printing each
key step as `office-gui-key: <key> -> <selected_ref>`.

Spec: `test/01_unit/app/office/sheet_gui_session_spec.spl`'s "keyboard"
describe block (7 new `it`s, all green, deliberate-fail probe run) covers:
arrow-key loop-back movement, edge clamp, hidden-row skip (both
directions), typed-buffer accumulation + dump marker, enter-commits-and-
recalculates, escape-cancels, backspace-trims.

Residual at the time of this addendum (now updated by "Resolution part 3"
above, 2026-07-04): item #1 from "What would close this gap" above
(per-cell `table_widget` grid) was closed the same day by "Resolution part
2". Item #4 (real OS keyboard/mouse input) is now DONE for TERMINAL input —
`office sheet-gui-live` bridges real termios keystrokes into
`session_key` via `run_gui_live_step`, the same input device
`run_sheet_tui_mode` already used for the TUI-grid backend. `session_click`
remains a scripted entry point (no OS mouse device exists for a terminal to
bridge from). The one item that remains open for whichever lane wires a
real OS window: a windowed/compositor GUI backend's mouse+keyboard event
source feeding `common.ui.event`'s `UIEvent`s (or `session_click`/
`session_key`) — out of scope for the office/terminal lane.

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
4. Feed real OS mouse/keyboard input into `UIEvent`s. DONE for terminal
   keyboard input (2026-07-04, see "Resolution part 3" above) —
   `office sheet-gui-live` / `run_sheet_gui_live` bridges real termios
   keystrokes into `SheetGuiSession` via `run_gui_live_step`/`session_key`,
   the same input device `run_sheet_tui_mode` already used for the TUI-grid
   backend (still not via `common.ui.event`'s `UIEvent` variants —
   `session_key` remains the chosen session-level translator, per the
   "Keyboard interaction" comment block in `gui.spl`). Remaining: a
   windowed/compositor GUI backend's real mouse+keyboard event source
   (`os/` layer), out of scope here.
