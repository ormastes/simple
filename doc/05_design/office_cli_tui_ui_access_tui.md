<!-- codex-design -->
# Office Calc CLI/TUI UI Design

## Scope

This design covers the selected F1/N1 Calc TUI launched by:

```text
simple office calc [FILE] --tui
```

The semantic UI surface and the terminal frame expose the same controller
state. The design does not redesign Writer, Impress, or the IDE GUI.

## Deterministic 124x37 Capture

```text
┌ Simple Calc — formulas.xlsx ────────────────────────────────────────────────┐
│ Name box: A1     Formula: [ 6                                      ] [Enter]│
├────┬──────────────┬──────────────┬──────────────┬───────────────────────────┤
│    │ A            │ B            │ C            │ D                         │
├────┼──────────────┼──────────────┼──────────────┼───────────────────────────┤
│  1 │ 6            │ 48           │ 7            │                           │
│  2 │ 8            │              │              │                           │
│  3 │              │              │              │                           │
│  4 │              │              │              │                           │
│  5 │              │              │              │                           │
│    │              │              │              │                           │
│    │              │              │              │                           │
├────┴──────────────┴──────────────┴──────────────┴───────────────────────────┤
│ Sheet1 | Ready | A1 selected | Ctrl+S save | arrows move | q quit           │
└─────────────────────────────────────────────────────────────────────────────┘
```

The actual ANSI capture includes clear/home and style sequences. A normalized
text companion strips ANSI only for manual embedding and assertions.

## Interaction Model

| Operator intent | Semantic target | Action | Result |
|---|---|---|---|
| Select A1 | `main#cell_A1` | `select` | A1 focused/selected; formula input reflects A1 |
| Enter a value/formula | `main#formula_input` | `type_text` or `set_value` | Pending edit buffer changes |
| Commit | `main#confirm_edit` | `invoke` | Sheet mutates, formulas recalculate, revision advances |
| Inspect result | `main#cell_B1` / `main#cell_C1` | read through snapshot/find | Display values are 48 and 7 |

Keyboard input and semantic actions route to the same controller transitions.
The semantic route must not simulate terminal coordinates or inject private
sheet mutations.

## Operator/LLM Flow

1. Launch Calc with the deployed Office command.
2. Run `simple ui windows --json` and find surface `main`.
3. Run `snapshot` and `surface main`.
4. Find `main#cell_A1`, `main#formula_input`, and `main#confirm_edit`.
5. Select A1, type `6`, and confirm.
6. Select A2, type `8`, and confirm.
7. Select B1, type `=A1*A2`, and confirm.
8. Select C1, type `=AVG(A1:A2)`, and confirm.
9. Read a new snapshot and verify B1=`48`, C1=`7`.
10. Read history and verify correlated request/action/result records.
11. Capture the final 124x37 ANSI and normalized text frame.

## Semantic States

- `selected`: exactly one active cell in the visible grid.
- `focused`: formula input while editing, otherwise the active cell.
- `editing`: true after value-bearing input and before confirmation.
- `enabled`: confirmation is enabled only for a pending edit.
- `text_value`: cell display value for grid cells; raw pending value for formula
  input.
- properties: cell reference, raw formula/value, cached display, sheet name,
  snapshot revision.

## Visual Evidence

Evidence root:

`build/test-artifacts/03_system/app/office/feature/office_cli_tui_ui_access/`

Required captures:

- `tui/calc-before.ansi`
- `tui/calc-before.txt`
- `tui/calc-after.ansi`
- `tui/calc-after.txt`

The final capture must visibly contain A1=`6`, A2=`8`, B1=`48`, C1=`7`, the
active reference, and the Calc title. Semantic JSON is the behavior oracle;
ANSI/text is visual confirmation. Calc uses the established SheetsApp viewport:
20 sheet columns by 30 sheet rows, rendered in a 124x37 terminal frame.

## Error Presentation

- Invalid formula: retain the typed formula and show the existing `#ERR`
  display/status.
- Stale target: do not change the visible frame; CLI reports `stale_target`.
- Unsupported action: do not change focus/edit state; CLI reports
  `unsupported_action`.
- Missing file: explicit diagnostic when a path was provided; no-file form
  opens a new workbook.
- Service unavailable: Calc remains usable by keyboard while `simple ui`
  reports `source_unavailable`.

## Accessibility and Determinism

- Cell identity is reference-based, never coordinate-only.
- Row/column headers and formula/status text remain visible in normalized
  captures.
- Stable node order is root, controls, then visible cells in row-major order.
- Capture width/height, fixture values, sheet name, and evidence filenames are
  frozen by the system-test plan.
