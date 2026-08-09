# Office Calc TUI Operation for LLM Tools

## Canonical Size

Calc preserves the established `SheetsApp` viewport of 20 sheet columns by 30
sheet rows. The fixed terminal/evidence frame is 124 columns by 37 rows:

- 4 columns for row numbers;
- 20 cell columns at 6 terminal columns each;
- 7 rows for title, active-cell/formula information, spacing, header, sheet
  tabs/status, and final state.

A 6x8 or similarly reduced grid is a UI regression. A blank process launch is
not evidence.

## Launch Rule

For development, use the existing pure-Simple runtime to launch the executable
Office owner. Do not bootstrap merely to test an Office application change.
Do not launch `src/app/cli/main.spl` as UI evidence because it is a re-export
module; use the Office command owner or a compiled CLI application artifact.

The preferred installed command remains:

```text
simple office calc [FILE] --tui
```

For semantic LLM/debug access, launch the opt-in loopback service on an
available port and point the normal `simple ui` client at that endpoint:

```text
simple office calc [FILE] --tui --ui-access-port PORT
```

Do not call a controller in-process or reuse prior artifacts as an operator
test. The service process, UI-client commands, and rendered terminal must all
belong to the same fresh run ID.

## LLM Inspection Flow

1. Launch Calc in a PTY of at least 124x37.
2. Confirm the screen is non-empty and shows `Simple Calc`.
3. Confirm the visible grid spans A through T and rows 1 through 30.
4. Use semantic discovery in this order: windows, snapshot, surface, find.
5. Act through stable IDs such as `main#cell_A1`,
   `main#formula_input`, and `main#confirm_edit`.
6. Verify results from an independent post-action snapshot and correlated
   history.
7. Retain a 124x37 text/ANSI capture. Do not pad a smaller UI and claim it was
   full-size; the source render itself must contain the full grid.

## Formula Smoke

Enter A1=6, A2=8, B1=`=A1*A2`, and C1=`=AVG(A1:A2)`. The TUI and semantic
snapshot must independently show B1=48 and C1=7.
