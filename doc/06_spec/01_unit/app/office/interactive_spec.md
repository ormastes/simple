# interactive_spec

> Interactive sheet editor spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interactive_spec

Interactive sheet editor spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/interactive_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Interactive sheet editor spec.

The editor's command core (`editor_apply`) is pure over (Sheet, line):
set/get/del recalculate live, show renders the ASCII grid, quit ends the
session. This is the same surface the stdin loop drives.

## Scenarios

### interactive editor: command core

#### sets cells and computes formulas live

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("e")
var step = editor_apply(sh, "set A1 10")
step = editor_apply(step.sheet, "set A2 32")
step = editor_apply(step.sheet, "set A3 =A1+A2")
expect(step.reply).to_equal("A3 = 42")
step = editor_apply(step.sheet, "get A3")
expect(step.reply).to_equal("A3 = 42")
expect(step.quit).to_be(false)
```

</details>

#### renders the grid with column letters and row numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("e")
var step = editor_apply(sh, "set A1 hi")
step = editor_apply(step.sheet, "set B2 7")
val view = sheet_grid_text(step.sheet)
expect(view).to_contain("A")
expect(view).to_contain("B")
expect(view).to_contain("hi")
expect(view).to_contain("7")
```

</details>

#### deletes cells and recalculates dependents

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("e")
var step = editor_apply(sh, "set A1 5")
step = editor_apply(step.sheet, "set A2 =A1*2")
expect(step.reply).to_equal("A2 = 10")
step = editor_apply(step.sheet, "del A1")
step = editor_apply(step.sheet, "get A2")
expect(step.reply).to_equal("A2 = 0")
```

</details>

#### renders a full-screen ANSI frame with title, grid, and status bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("e")
var step = editor_apply(sh, "set A1 42")
val frame = sheet_screen_frame(step.sheet, "budget.csv", "Ready")
expect(frame).to_contain("[2J")
expect(frame).to_contain("[7m")
expect(frame).to_contain("budget.csv")
expect(frame).to_contain("42")
expect(frame).to_contain("Ready")
expect(frame).to_contain("calc>")
```

</details>

#### keystrokes: typing + Enter commits a cell with live recalculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = tui_new_state(Sheet.new("t"))
s = tui_apply_key(s, 52)   # '4'
s = tui_apply_key(s, 50)   # '2'
s = tui_apply_key(s, 10)   # Enter -> A1=42, cursor A2
s = tui_apply_key(s, 61)   # '='
s = tui_apply_key(s, 65)   # 'A'
s = tui_apply_key(s, 49)   # '1'
s = tui_apply_key(s, 42)   # '*'
s = tui_apply_key(s, 50)   # '2'
s = tui_apply_key(s, 10)   # Enter -> A2==A1*2 -> 84
expect(s.status).to_contain("A2 = 84")
```

</details>

#### keystrokes: arrow escape sequences move the cursor, q quits

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = tui_new_state(Sheet.new("t"))
s = tui_apply_key(s, 27)   # ESC
s = tui_apply_key(s, 91)   # [
s = tui_apply_key(s, 67)   # C -> right
expect(s.cur.col).to_equal(1)
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 66)   # B -> down
expect(s.cur.row).to_equal(1)
s = tui_apply_key(s, 113)  # q
expect(s.quit).to_be(true)
```

</details>

#### keystrokes: the TUI frame shows the buffer in the formula bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = tui_new_state(Sheet.new("t"))
s = tui_apply_key(s, 104)  # h
s = tui_apply_key(s, 105)  # i
val frame = tui_frame(s, "f.csv")
expect(frame).to_contain("[A1] hi")
expect(frame).to_contain("[2J")
```

</details>

#### rejects invalid refs and unknown commands; quit ends the session

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("e")
val bad_ref = editor_apply(sh, "set 9X 1")
expect(bad_ref.reply).to_start_with("error:")
val unknown = editor_apply(sh, "frobnicate")
expect(unknown.reply).to_contain("unknown command")
val quit_step = editor_apply(sh, "quit")
expect(quit_step.quit).to_be(true)
val eof_step = editor_apply(sh, "")
expect(eof_step.quit).to_be(true)
```

</details>

### interactive editor: hidden-row cursor awareness

#### down-arrow skips a hidden row instead of landing on it

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
sh.hide_row(2)
var s = tui_new_state(sh)
s = tui_apply_key(s, 27)   # ESC
s = tui_apply_key(s, 91)   # [
s = tui_apply_key(s, 66)   # B -> down
expect(s.cur.row).to_equal(2)   # row index 2 == 1-based row 3
```

</details>

#### up-arrow skips a hidden row instead of landing on it

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
sh.hide_row(2)
var s = tui_new_state(sh)
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 66)   # down -> row 2
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 65)   # A -> up, must return to row 0
expect(s.cur.row).to_equal(0)
```

</details>

#### skips a run of consecutive hidden rows in one keypress

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
sh.hide_row(2)
sh.hide_row(3)
sh.hide_row(4)
var s = tui_new_state(sh)
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 66)
expect(s.cur.row).to_equal(4)   # 1-based row 5
```

</details>

#### stays put when every row below the cursor is hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
var r = 2
while r <= 100:
    sh.hide_row(r.to_i64())
    r = r + 1
var s = tui_new_state(sh)
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 66)
expect(s.cur.row).to_equal(0)
```

</details>

#### leaves horizontal movement untouched by hidden rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
sh.hide_row(2)
var s = tui_new_state(sh)
s = tui_apply_key(s, 27)
s = tui_apply_key(s, 91)
s = tui_apply_key(s, 67)   # C -> right
expect(s.cur.col).to_equal(1)
expect(s.cur.row).to_equal(0)
```

</details>

### interactive editor: hide/unhide row commands

#### hide removes the row from the rendered grid, unhide restores it

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
var step = editor_apply(sh, "set A1 top")
step = editor_apply(step.sheet, "set A2 middle")
step = editor_apply(step.sheet, "set A3 bottom")
expect(sheet_grid_text(step.sheet)).to_contain("middle")
step = editor_apply(step.sheet, "hide 2")
expect(step.reply).to_equal("hid row 2")
val hidden_view = sheet_grid_text(step.sheet)
expect(hidden_view.contains("middle")).to_equal(false)
expect(hidden_view).to_contain("top")
expect(hidden_view).to_contain("bottom")
step = editor_apply(step.sheet, "unhide 2")
expect(step.reply).to_equal("unhid row 2")
expect(sheet_grid_text(step.sheet)).to_contain("middle")
```

</details>

#### hiding a row does not delete its data

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
var step = editor_apply(sh, "set A2 keepme")
step = editor_apply(step.sheet, "hide 2")
step = editor_apply(step.sheet, "get A2")
expect(step.reply).to_equal("A2 = keepme")
```

</details>

#### hidden rows still feed formulas

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
var step = editor_apply(sh, "set A1 10")
step = editor_apply(step.sheet, "set A2 32")
step = editor_apply(step.sheet, "hide 2")
step = editor_apply(step.sheet, "set B1 =A1+A2")
expect(step.reply).to_equal("B1 = 42")
```

</details>

#### rejects a non-numeric or out-of-range row

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
expect(editor_apply(sh, "hide zero").reply).to_start_with("error:")
expect(editor_apply(sh, "hide 0").reply).to_start_with("error:")
expect(editor_apply(sh, "hide -1").reply).to_start_with("error:")
expect(editor_apply(sh, "unhide 99999").reply).to_start_with("error:")
```

</details>

#### hide is idempotent and unhide of a visible row is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = Sheet.new("h")
var step = editor_apply(sh, "set A1 x")
step = editor_apply(step.sheet, "hide 1")
step = editor_apply(step.sheet, "hide 1")
expect(step.reply).to_equal("hid row 1")
step = editor_apply(step.sheet, "unhide 1")
step = editor_apply(step.sheet, "unhide 1")
expect(step.reply).to_equal("unhid row 1")
expect(sheet_grid_text(step.sheet)).to_contain("x")
```

</details>

#### advertises the new commands in help

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reply = editor_apply(Sheet.new("h"), "help").reply
expect(reply).to_contain("hide <row>")
expect(reply).to_contain("unhide <row>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
