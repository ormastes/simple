# Terminal Emulator Unit Tests

> Tests for TerminalChar, TerminalLine, and Terminal class:

<!-- sdn-diagram:id=terminal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_spec -> std
terminal_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Emulator Unit Tests

Tests for TerminalChar, TerminalLine, and Terminal class:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/terminal/terminal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for TerminalChar, TerminalLine, and Terminal class:
    construction, write_char, newline, scroll_up, clear, ANSI parsing.

    This describe block exercises the TerminalChar value type that
    holds a single screen cell (char + fg/bg color + bold flag).

## Scenarios

### TerminalChar

#### constructs with default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = TerminalChar(ch: " ", fg: 7, bg: 0, bold: false)
expect(ch.ch).to_equal(" ")
expect(ch.fg).to_equal(7)
expect(ch.bg).to_equal(0)
expect(ch.bold).to_equal(false)
```

</details>

#### constructs with custom color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = TerminalChar(ch: "A", fg: 1, bg: 4, bold: true)
expect(ch.ch).to_equal("A")
expect(ch.fg).to_equal(1)
expect(ch.bg).to_equal(4)
expect(ch.bold).to_equal(true)
```

</details>

#### default_char returns space with white-on-black

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = default_char()
expect(ch.ch).to_equal(" ")
expect(ch.fg).to_equal(7)
expect(ch.bg).to_equal(0)
expect(ch.bold).to_equal(false)
```

</details>

### TerminalLine

#### new_line creates line with correct width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = new_line(80)
expect(line.chars.len()).to_equal(80)
```

</details>

#### new_line fills with blank chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = new_line(10)
expect(line.chars[0].ch).to_equal(" ")
expect(line.chars[9].ch).to_equal(" ")
```

</details>

#### line_to_text renders plain text

1. var line = new line
2. line chars[0] = TerminalChar
3. line chars[1] = TerminalChar


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var line = new_line(5)
line.chars[0] = TerminalChar(ch: "H", fg: 7, bg: 0, bold: false)
line.chars[1] = TerminalChar(ch: "i", fg: 7, bg: 0, bold: false)
val text_out = line_to_text(line)
expect(text_out).to_start_with("Hi")
```

</details>

### Terminal

#### when newly created

#### has correct cols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.cols).to_equal(80)
```

</details>

#### has correct rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.rows).to_equal(25)
```

</details>

#### starts with cursor at row 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.cursor_row).to_equal(0)
```

</details>

#### starts with cursor at col 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.cursor_col).to_equal(0)
```

</details>

#### has correct number of lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.lines.len()).to_equal(25)
```

</details>

#### starts with default fg color (white)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.fg_color).to_equal(7)
```

</details>

#### starts with default bg color (black)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.bg_color).to_equal(0)
```

</details>

#### starts not bold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.bold).to_equal(false)
```

</details>

#### starts with empty input buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.input_buffer).to_equal("")
```

</details>

#### starts with empty output buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.output_buffer).to_equal("")
```

</details>

#### starts with ANSI state Normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.ansi_state).to_equal(AnsiState.Normal)
```

</details>

#### starts with max_scrollback of 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.max_scrollback).to_equal(1000)
```

</details>

#### with small dimensions

#### creates 1x1 terminal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(1, 1)
expect(term.cols).to_equal(1)
expect(term.rows).to_equal(1)
expect(term.lines.len()).to_equal(1)
```

</details>

### Terminal write_char

#### places character at cursor position

1. var term = Terminal new
2. term write char
   - Expected: ch.ch equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_char("A")
val ch = term.lines[0].chars[0]
expect(ch.ch).to_equal("A")
```

</details>

#### advances cursor column after write

1. var term = Terminal new
2. term write char
   - Expected: term.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_char("A")
expect(term.cursor_col).to_equal(1)
```

</details>

#### writes multiple characters sequentially

1. var term = Terminal new
2. term write char
3. term write char
   - Expected: term.cursor_col equals `2`
   - Expected: term.lines[0].chars[0].ch equals `H`
   - Expected: term.lines[0].chars[1].ch equals `i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_char("H")
term.write_char("i")
expect(term.cursor_col).to_equal(2)
expect(term.lines[0].chars[0].ch).to_equal("H")
expect(term.lines[0].chars[1].ch).to_equal("i")
```

</details>

#### wraps at end of line

1. var term = Terminal new
2. term write char
3. term write char
4. term write char


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(3, 2)
term.write_char("A")
term.write_char("B")
term.write_char("C")
# After writing 3 chars in a 3-col terminal, cursor should wrap
expect(term.cursor_row).to_be_greater_than(0)
```

</details>

#### handles newline character

1. var term = Terminal new
2. term write char
3. term write char
   - Expected: term.cursor_row equals `1`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_char("A")
term.write_char("\n")
expect(term.cursor_row).to_equal(1)
expect(term.cursor_col).to_equal(0)
```

</details>

### Terminal newline

#### moves cursor to next row

1. var term = Terminal new
2. term newline
   - Expected: term.cursor_row equals `1`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.newline()
expect(term.cursor_row).to_equal(1)
expect(term.cursor_col).to_equal(0)
```

</details>

#### resets cursor_col to 0

1. var term = Terminal new
2. term write char
3. term write char
4. term newline
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_char("X")
term.write_char("Y")
term.newline()
expect(term.cursor_col).to_equal(0)
```

</details>

#### scrolls when at last row

1. var term = Terminal new
2. term newline
   - Expected: term.cursor_row equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 3)
term.cursor_row = 2
term.newline()
# After newline at last row, cursor stays at last row
expect(term.cursor_row).to_equal(2)
```

</details>

### Terminal scroll_up

#### shifts buffer up by one line

1. var term = Terminal new
2. term lines[0] chars[0] = TerminalChar
3. term lines[1] chars[0] = TerminalChar
4. term lines[2] chars[0] = TerminalChar
5. term scroll up
   - Expected: term.lines[0].chars[0].ch equals `B`
   - Expected: term.lines[1].chars[0].ch equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(10, 3)
term.lines[0].chars[0] = TerminalChar(ch: "A", fg: 7, bg: 0, bold: false)
term.lines[1].chars[0] = TerminalChar(ch: "B", fg: 7, bg: 0, bold: false)
term.lines[2].chars[0] = TerminalChar(ch: "C", fg: 7, bg: 0, bold: false)
term.scroll_up()
# Line 0 should now be what was line 1
expect(term.lines[0].chars[0].ch).to_equal("B")
expect(term.lines[1].chars[0].ch).to_equal("C")
```

</details>

#### adds blank line at bottom after scroll

1. var term = Terminal new
2. term lines[2] chars[0] = TerminalChar
3. term scroll up
   - Expected: term.lines[2].chars[0].ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(10, 3)
term.lines[2].chars[0] = TerminalChar(ch: "X", fg: 7, bg: 0, bold: false)
term.scroll_up()
# Last line should be blank
expect(term.lines[2].chars[0].ch).to_equal(" ")
```

</details>

#### preserves line count after scroll

1. var term = Terminal new
2. term scroll up
   - Expected: term.lines.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(10, 5)
term.scroll_up()
expect(term.lines.len()).to_equal(5)
```

</details>

### Terminal clear

#### resets all lines to blank

1. var term = Terminal new
2. term write char
3. term write char
4. term clear
   - Expected: term.lines[0].chars[0].ch equals ` `
   - Expected: term.lines[0].chars[1].ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(10, 3)
term.write_char("A")
term.write_char("B")
term.clear()
expect(term.lines[0].chars[0].ch).to_equal(" ")
expect(term.lines[0].chars[1].ch).to_equal(" ")
```

</details>

#### resets cursor to origin

1. var term = Terminal new
2. term clear
   - Expected: term.cursor_row equals `0`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.cursor_row = 10
term.cursor_col = 20
term.clear()
expect(term.cursor_row).to_equal(0)
expect(term.cursor_col).to_equal(0)
```

</details>

#### preserves number of lines

1. var term = Terminal new
2. term clear
   - Expected: term.lines.len() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.clear()
expect(term.lines.len()).to_equal(25)
```

</details>

### Terminal ANSI parsing

#### starts in Normal state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = Terminal.new(80, 25)
expect(term.ansi_state).to_equal(AnsiState.Normal)
```

</details>

#### AnsiState enum has Normal variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AnsiState.Normal
expect(state).to_equal(AnsiState.Normal)
```

</details>

#### AnsiState enum has Escape variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AnsiState.Escape
expect(state).to_equal(AnsiState.Escape)
```

</details>

#### AnsiState enum has Bracket variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AnsiState.Bracket
expect(state).to_equal(AnsiState.Bracket)
```

</details>

#### AnsiState enum has Param variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AnsiState.Param
expect(state).to_equal(AnsiState.Param)
```

</details>

### Terminal write_string

#### writes multiple characters

1. var term = Terminal new
2. term write string
   - Expected: term.cursor_col equals `5`
   - Expected: term.lines[0].chars[0].ch equals `H`
   - Expected: term.lines[0].chars[4].ch equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_string("Hello")
expect(term.cursor_col).to_equal(5)
expect(term.lines[0].chars[0].ch).to_equal("H")
expect(term.lines[0].chars[4].ch).to_equal("o")
```

</details>

#### handles embedded newlines

1. var term = Terminal new
2. term write string
   - Expected: term.lines[0].chars[0].ch equals `A`
   - Expected: term.lines[0].chars[1].ch equals `B`
   - Expected: term.lines[1].chars[0].ch equals `C`
   - Expected: term.lines[1].chars[1].ch equals `D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var term = Terminal.new(80, 25)
term.write_string("AB\nCD")
expect(term.lines[0].chars[0].ch).to_equal("A")
expect(term.lines[0].chars[1].ch).to_equal("B")
expect(term.lines[1].chars[0].ch).to_equal("C")
expect(term.lines[1].chars[1].ch).to_equal("D")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
