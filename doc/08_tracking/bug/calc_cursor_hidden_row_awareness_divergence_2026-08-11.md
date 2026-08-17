# Calc cursor movement: only the GUI session honours hidden rows

**Date:** 2026-08-11
Status: RESOLVED 2026-08-17 — all three cursor paths are hidden-row aware.
History: OPEN -> PARTIALLY FIXED 2026-08-17 (`ff66bac92f85`, TUI) -> RESOLVED
2026-08-17 (`10da1bf0f786`, `SheetsApp.navigate_to`).
2026-08-17 (this commit, `SheetsApp.navigate_to`).

## Resolution 2026-08-17

The third and last path, `SheetsApp.navigate_to`
(`src/app/office/sheets/sheets_app.spl`), now skips hidden rows with the exact
semantics of the other two: step in the SAME direction of travel until a
visible row is found; on hitting the grid edge first, stay on the row the
cursor came from (never wraps); a pure-horizontal move (`Tab`,
`ArrowLeft/Right`) leaves the row untouched, because the direction is inferred
from the delta against the current active cell and a zero delta skips the scan
entirely. The 1-based/0-based mismatch is handled at the single query site
(`is_row_hidden((scan + 1).to_i64())` against a 0-based `CellRef.row`).

### The frozen-contract blocker in "Why this was not fixed by merging" is void

Blocker 2 above assumed hidden-row skipping would change
`CalcAccessController.tui_text()`, the frozen `office_cli_tui_ui_access`
acceptance output. It does not, for two independent reasons:

1. The scan only fires when the TARGET row is hidden. An absolute jump onto a
   visible row — the only kind the controller's cell `select`
   (`access_controller.spl:314`) can produce, since a hidden row is not
   rendered and so cannot be clicked — is bit-for-bit unchanged.
2. Neither the controller nor the frozen spec ever hides a row:
   `grep -c "hide_row\|hidden" src/app/office/sheets/access_controller.spl
   doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md`
   returns `0` for both. There is no golden output to re-baseline.

### Evidence

Reproducing spec (new):
`test/01_unit/app/office/sheets/sheets_app_hidden_row_nav_spec.spl`

```
RED   (before the fix): Results: 6 total, 0 passed, 6 failed
GREEN (after the fix):  Results: 6 total, 6 passed, 0 failed
```

The RED failures were genuine assertions, not a harness error — every one
reported `expected 1 to equal N`, i.e. the cursor parked on row index 1, the
hidden row.

Defect-CLASS spec (new):
`test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl`

```
GREEN: Results: 6 total, 6 passed, 0 failed
```

This one exists because the recurring defect is not "path X is broken" but "a
NEW cursor-movement entry point forgot hidden-row awareness" — which happened
three times, and was found and fixed three separate times. It drives ALL THREE
paths over ONE fixture through a single `_all_paths` helper and asserts the
joint invariant: (I1) no path leaves the cursor on a hidden row, (I2) all
paths agree on the landing row so divergence cannot reappear silently, (I3)
every path stays put at a grid edge with no visible row left. A fourth entry
point is covered the moment it is added to `_all_paths`.

Non-regression on the two already-fixed paths:

```
test/01_unit/app/office/sheet_gui_session_spec.spl  Results: 31 total, 31 passed, 0 failed
test/01_unit/app/office/interactive_spec.spl        Results: 19 total, 19 passed, 0 failed
```

### Residual (does not reopen this row)

`test/01_unit/app/office/sheets/access_controller_spec.spl` could not be run to
a verdict on this host: three attempts ended `reason=daemon-no-response` /
`daemon-worker-timeout` with **no `Results:` line at all** under heavy load
(21-30 concurrent `simple` processes), so those runs are INCONCLUSIVE — never
read as a pass or a fail. The static argument above (the controller never hides
a row, and the scan is a no-op on a visible target) is why this is recorded
rather than treated as a blocker. Re-run when the box is quiet:

```
bin/simple test test/01_unit/app/office/sheets/access_controller_spec.spl
```
Status: OPEN (P2) — PARTIALLY FIXED 2026-08-17 (commit ff66bac92f85)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Partial fix 2026-08-17 — `ff66bac92f85`:** path 1 (`_tui_move`,
`src/app/office/interactive.spl`) is now hidden-row aware. Evidence: grepped
`_tui_move` in the current tree — its body calls
`s.sheet.is_row_hidden((scan + 1).to_i64())` in a same-direction skip loop that
falls back to the original row at the grid edge (no wrap), matching
`_sheet_gui_move_within_bounds`. Path 2 (`SheetsApp.navigate_to`,
`src/app/office/sheets/sheets_app.spl`) is **still not** hidden-row aware —
grep for `is_row_hidden` in its body returns nothing — so this row stays OPEN
until that path converges or is deliberately exempted.
**Area:** app/office (Calc)
**Severity:** Medium — a user-visible correctness gap on two of three surfaces

## Summary

Calc moves the cursor through three separate code paths. Only one of them,
`session_select` in `src/app/office/gui.spl`, skips hidden rows. The other two
walk row numbers arithmetically and will happily land the cursor on, or scroll
the viewport to, a row the user has hidden.

A prior dedupe sweep flagged these three as duplicate cursor logic. **They must
not be merged.** They are not three copies of one function, and merging them as
they stand would silently drop the hidden-row feature. This record exists so the
divergence is tracked rather than normalised away.

## The three paths

| Path | File | Receiver | Addressing | Scroll policy | Hidden-row aware |
|------|------|----------|-----------|---------------|------------------|
| `_tui_move(state, d_col, d_row)` | `src/app/office/interactive.spl:202` | `TuiState` | relative delta | none — `TuiState` has no viewport state at all | **No** |
| `SheetsApp.navigate_to(col, row)` | `src/app/office/sheets/sheets_app.spl:165` | `SheetsApp` | absolute `(col, row)` | naive window arithmetic on `scroll_row`/`scroll_col` | **Yes (2026-08-17)** |
| `session_select(session, ref_str, view_rows, view_cols)` | `src/app/office/gui.spl:1014` | `SheetGuiSession` | absolute A1-style ref string | minimal scroll over the *visible* row set | **Yes** |

Only the third consults `sheet.is_row_hidden`, and it does so indirectly:
`session_select` → `_sheet_gui_scroll_to_show_row` → `_sheet_gui_visible_rows`,
which forward-scans skipping every hidden row (`gui.spl:1280-1295`), bounded by
`OFFICE_GUI_SHEET_SCROLL_SCAN_LIMIT`.

The three also differ in ways unrelated to hidden rows: `session_select`
discards the pending edit buffer and returns a **new** session (copy semantics),
`navigate_to` additionally re-syncs `formula_text` from the newly active cell,
and `_tui_move` does neither.

## Why this was not fixed by merging

Both obvious repairs are blocked:

1. **Make `_tui_move` hidden-row aware.** `TuiState` (`interactive.spl:190-197`)
   carries `sheet`, `cur`, `buffer`, `status`, `pending_esc`, `quit`, `dirty` —
   no scroll origin. The terminal editor renders a fixed viewport anchored at
   A1. Adding hidden-row skipping means inventing viewport state and changing
   what the TUI paints.
2. **Make `navigate_to` hidden-row aware.** `navigate_to` is what the UI-access
   controller calls on every cell `select`
   (`access_controller.spl:151`). Its `scroll_row`/`scroll_col` feed
   `CalcAccessController.tui_text()`, whose rendered output is the **frozen
   acceptance contract** of the in-flight `office_cli_tui_ui_access` deliverable.
   Skipping hidden rows would change that output whenever a row is hidden.

So the honest disposition is to record the divergence rather than to either
merge (dropping a feature) or unilaterally change a frozen contract.

## Reproduction

Hide a row, then move the cursor across it on each surface:

- `session_select` — the hidden row is skipped; the viewport scrolls the minimum
  amount to reveal the next *visible* row.
- `navigate_to` / `_tui_move` — the cursor lands on the hidden row, and
  `navigate_to` will scroll the viewport to a row that renders as hidden.

## Suggested fix

Decide the intended semantics once, then converge deliberately:

1. Confirm with the `office_cli_tui_ui_access` owner whether hidden-row skipping
   belongs inside the frozen contract. If it does, the contract and its golden
   output must be re-baselined in the same change.
2. Give `SheetsApp` the visible-row primitive that `gui.spl` already has (extract
   `_sheet_gui_visible_rows` / `_sheet_gui_visible_rows_before` into a shared
   `app.office.sheets` module, the same way `office_grid_body` was extracted).
3. Only then consider collapsing the call sites — and only the ones that truly
   share a receiver and addressing mode. `_tui_move` is a relative-delta
   operation on a viewport-less state and is unlikely to ever merge cleanly.

## Related

- `src/app/office/sheets/grid_render.spl` — the grid-body extraction landed
  alongside this record; that one *was* a genuine dedupe because the only
  difference was a parameterisable scroll origin.
- `doc/05_design/office_cli_tui_ui_access.md`
- `doc/06_spec/03_system/app/office/feature/office_cli_tui_ui_access_spec.md`

## Content re-verification 2026-08-17 (app-lane worker) — STILL OPEN

Classified by CONTENT of current source, not by commit ancestry:

```
$ /usr/bin/grep -nc "hidden" src/app/office/interactive.spl src/app/office/gui.spl
src/app/office/interactive.spl:0
src/app/office/gui.spl:32
```

`src/app/office/interactive.spl` contains the token `hidden` **zero** times, so
`_tui_move` cannot be hidden-row aware; `src/app/office/gui.spl` carries the
`is_row_hidden` logic at 32 sites (`gui.spl:214` `if not
sheet.is_row_hidden(r.to_i64()):`, plus the visible-row window contract at
`gui.spl:1268-1282`). The asymmetry the record describes is intact. No fix
applied by this worker; no spec written (would need a TUI-session harness).
