# vt_screen_spec

> For maintainers of smux and of the caret dashboard's agent screen. A full-screen

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vt_screen_spec

For maintainers of smux and of the caret dashboard's agent screen. A full-screen

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/smux/vt_screen_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
For maintainers of smux and of the caret dashboard's agent screen. A full-screen
program — an agent TUI, or ConPTY itself — does not print lines: it moves the
cursor and overwrites cells. `vt_screen` applies that output to a rows x cols
grid so a capture shows what the program currently displays, instead of every
frame it ever drew.
## Operator workflow
bin/simple test test/01_unit/os/apps/smux/vt_screen_spec.spl
## Compatibility and limitations
Covers the layout subset ConPTY and common TUIs emit: CUP/HVP, cursor moves,
CHA/VPA, erase-in-line/display, erase-chars, wrap and scroll. Colours, modes
and OSC titles are consumed. Unsupported sequences are ignored, never printed.
## Verification guidance and troubleshooting
A capture that shows stale dialog text after a redraw means an erase sequence
is not applied; text run together without spaces means cursor-forward is lost.

## Scenarios

### smux pane screen

#### overwrites a cell in place when the program moves the cursor back

- Print a dialog line, then redraw its first word at the same spot
- The screen shows the redraw, not both frames
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `Done  folder? yes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Print a dialog line, then redraw its first word at the same spot")
var s = vt_new(4, 20)
s = vt_feed(s, "Trust folder? yes")
s = vt_feed(s, esc() + "[1;1H" + "Done ")
step("The screen shows the redraw, not both frames")
expect(vt_text(s)).to_equal("Done  folder? yes")
```

</details>

#### turns a cursor-forward into the blank cells it skipped

- Write two words separated by a cursor-forward of three columns
- The skipped cells read as spaces
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `ab   cd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Write two words separated by a cursor-forward of three columns")
val s = vt_feed(vt_new(2, 20), "ab" + esc() + "[3C" + "cd")
step("The skipped cells read as spaces")
expect(vt_text(s)).to_equal("ab   cd")
```

</details>

#### erases the rest of a line and the whole display on request

- Fill two rows, erase from column 3 of row 1 to the end
- Row one keeps only what preceded the cursor
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `ab\nsecond`
- Erase the whole display
   - Expected: vt_text(s) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Fill two rows, erase from column 3 of row 1 to the end")
var s = vt_feed(vt_new(3, 10), "abcdefgh\r\nsecond")
s = vt_feed(s, esc() + "[1;3H" + esc() + "[K")
step("Row one keeps only what preceded the cursor")
expect(vt_text(s)).to_equal("ab\nsecond")
step("Erase the whole display")
s = vt_feed(s, esc() + "[2J")
expect(vt_text(s)).to_equal("")
```

</details>

#### wraps at the right edge and scrolls at the bottom

- Write more lines than the screen has rows
- Only the newest rows remain, and the long word wrapped
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `three\n45678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Write more lines than the screen has rows")
val s = vt_feed(vt_new(2, 5), "one\r\ntwo\r\nthree45678")
step("Only the newest rows remain, and the long word wrapped")
expect(vt_text(s)).to_equal("three\n45678")
```

</details>

#### keeps box drawing and other multi-byte characters whole

- Draw a box border, then overwrite its middle cell
- Exactly one character changed and no replacement characters appear
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `╭──●───╮`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Draw a box border, then overwrite its middle cell")
var s = vt_feed(vt_new(2, 10), "╭──────╮")
s = vt_feed(s, esc() + "[1;4H" + "●")
step("Exactly one character changed and no replacement characters appear")
expect(vt_text(s)).to_equal("╭──●───╮")
```

</details>

#### returns to a saved cursor position after drawing elsewhere

- Save the cursor, draw a status line at the bottom, restore, keep typing
- The input continues where it was, and the status stays at the bottom
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: vt_text(s) equals `> abcd\n\nstatus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Save the cursor, draw a status line at the bottom, restore, keep typing")
var s = vt_feed(vt_new(3, 12), "> ab")
s = vt_feed(s, esc() + "7" + esc() + "[3;1H" + "status" + esc() + "8" + "cd")
step("The input continues where it was, and the status stays at the bottom")
expect(vt_text(s)).to_equal("> abcd\n\nstatus")
```

</details>

#### drops colours, titles and modes instead of printing them

- Feed colours, a title, a private mode and a split escape sequence
- Only the printable text reaches the screen, even across reads
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: vt_text(s) equals `red!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SMUX-VT-001
step("Feed colours, a title, a private mode and a split escape sequence")
var s = vt_new(2, 20)
s = vt_feed(s, esc() + "]0;title" + "\x07" + esc() + "[?25l" + esc() + "[31mred" + esc() + "[")
s = vt_feed(s, "0m!")
step("Only the printable text reaches the screen, even across reads")
expect(vt_text(s)).to_equal("red!")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
