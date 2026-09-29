# Terminal Emulator Unit Tests

> Tests for TerminalChar, TerminalLine, and Terminal class:

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
| Source | `test/unit/os/apps/terminal/terminal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for TerminalChar, TerminalLine, and Terminal class:
    construction, write_char, newline, scroll_up, clear, ANSI parsing.

    This describe block exercises the TerminalChar value type that
    holds a single screen cell (char + fg/bg color + bold flag).

## Scenarios

### TerminalChar

#### constructs with default values

- constructs with default values
   - Expected: ch.ch equals ` `
   - Expected: ch.fg equals `7`
   - Expected: ch.bg equals `0`
   - Expected: ch.bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with default values")
"""TerminalChar(ch, fg, bg, bold) round-trips its fields unchanged."""
val ch = TerminalChar(ch: " ", fg: 7, bg: 0, bold: false)
expect(ch.ch).to_equal(" ")
expect(ch.fg).to_equal(7)
expect(ch.bg).to_equal(0)
expect(ch.bold).to_equal(false)
```

</details>

#### constructs with custom color

- constructs with custom color
   - Expected: ch.ch equals `A`
   - Expected: ch.fg equals `1`
   - Expected: ch.bg equals `4`
   - Expected: ch.bold is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with custom color")
val ch = TerminalChar(ch: "A", fg: 1, bg: 4, bold: true)
expect(ch.ch).to_equal("A")
expect(ch.fg).to_equal(1)
expect(ch.bg).to_equal(4)
expect(ch.bold).to_equal(true)
```

</details>

#### default_char returns space with white-on-black

- default_char returns space with white-on-black
   - Expected: ch.ch equals ` `
   - Expected: ch.fg equals `7`
   - Expected: ch.bg equals `0`
   - Expected: ch.bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_char returns space with white-on-black")
val ch = default_char()
expect(ch.ch).to_equal(" ")
expect(ch.fg).to_equal(7)
expect(ch.bg).to_equal(0)
expect(ch.bold).to_equal(false)
```

</details>

### TerminalLine

#### new_line creates line with correct width

- new_line creates line with correct width
   - Expected: line.chars.len() equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_line creates line with correct width")
val line = new_line(80)
expect(line.chars.len()).to_equal(80)
```

</details>

#### new_line fills with blank chars

- new_line fills with blank chars
   - Expected: line.chars[0].ch equals ` `
   - Expected: line.chars[9].ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new_line fills with blank chars")
val line = new_line(10)
expect(line.chars[0].ch).to_equal(" ")
expect(line.chars[9].ch).to_equal(" ")
```

</details>

#### line_to_text renders plain text

- line_to_text renders plain text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("line_to_text renders plain text")
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

- has correct cols
   - Expected: term.cols equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct cols")
val term = Terminal.new(80, 25)
expect(term.cols).to_equal(80)
```

</details>

#### has correct rows

- has correct rows
   - Expected: term.rows equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct rows")
val term = Terminal.new(80, 25)
expect(term.rows).to_equal(25)
```

</details>

#### starts with cursor at row 0

- starts with cursor at row 0
   - Expected: term.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with cursor at row 0")
val term = Terminal.new(80, 25)
expect(term.cursor_row).to_equal(0)
```

</details>

#### starts with cursor at col 0

- starts with cursor at col 0
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with cursor at col 0")
val term = Terminal.new(80, 25)
expect(term.cursor_col).to_equal(0)
```

</details>

#### has correct number of lines

- has correct number of lines
   - Expected: term.lines.len() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct number of lines")
val term = Terminal.new(80, 25)
expect(term.lines.len()).to_equal(25)
```

</details>

#### starts with default fg color (white)

- starts with default fg color (white)
   - Expected: term.fg_color equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with default fg color (white)")
val term = Terminal.new(80, 25)
expect(term.fg_color).to_equal(7)
```

</details>

#### starts with default bg color (black)

- starts with default bg color (black)
   - Expected: term.bg_color equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with default bg color (black)")
val term = Terminal.new(80, 25)
expect(term.bg_color).to_equal(0)
```

</details>

#### starts not bold

- starts not bold
   - Expected: term.bold is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts not bold")
val term = Terminal.new(80, 25)
expect(term.bold).to_equal(false)
```

</details>

#### starts with empty input buffer

- starts with empty input buffer
   - Expected: term.input_buffer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty input buffer")
val term = Terminal.new(80, 25)
expect(term.input_buffer).to_equal("")
```

</details>

#### starts with empty output buffer

- starts with empty output buffer
   - Expected: term.output_buffer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty output buffer")
val term = Terminal.new(80, 25)
expect(term.output_buffer).to_equal("")
```

</details>

#### starts with ANSI state Normal

- starts with ANSI state Normal
   - Expected: term.ansi_state equals `AnsiState.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with ANSI state Normal")
val term = Terminal.new(80, 25)
expect(term.ansi_state).to_equal(AnsiState.Normal)
```

</details>

#### starts with max_scrollback of 1000

- starts with max_scrollback of 1000
   - Expected: term.max_scrollback equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with max_scrollback of 1000")
val term = Terminal.new(80, 25)
expect(term.max_scrollback).to_equal(1000)
```

</details>

#### with small dimensions

#### creates 1x1 terminal

- creates 1x1 terminal
   - Expected: term.cols equals `1`
   - Expected: term.rows equals `1`
   - Expected: term.lines.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates 1x1 terminal")
val term = Terminal.new(1, 1)
expect(term.cols).to_equal(1)
expect(term.rows).to_equal(1)
expect(term.lines.len()).to_equal(1)
```

</details>

### Terminal write_char

#### places character at cursor position

- places character at cursor position
   - Expected: ch.ch equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places character at cursor position")
var term = Terminal.new(80, 25)
term.write_char("A")
val ch = term.lines[0].chars[0]
expect(ch.ch).to_equal("A")
```

</details>

#### advances cursor column after write

- advances cursor column after write
   - Expected: term.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances cursor column after write")
var term = Terminal.new(80, 25)
term.write_char("A")
expect(term.cursor_col).to_equal(1)
```

</details>

#### writes multiple characters sequentially

- writes multiple characters sequentially
   - Expected: term.cursor_col equals `2`
   - Expected: term.lines[0].chars[0].ch equals `H`
   - Expected: term.lines[0].chars[1].ch equals `i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes multiple characters sequentially")
var term = Terminal.new(80, 25)
term.write_char("H")
term.write_char("i")
expect(term.cursor_col).to_equal(2)
expect(term.lines[0].chars[0].ch).to_equal("H")
expect(term.lines[0].chars[1].ch).to_equal("i")
```

</details>

#### wraps at end of line

- wraps at end of line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps at end of line")
var term = Terminal.new(3, 2)
term.write_char("A")
term.write_char("B")
term.write_char("C")
# After writing 3 chars in a 3-col terminal, cursor should wrap
expect(term.cursor_row).to_be_greater_than(0)
```

</details>

#### handles newline character

- handles newline character
   - Expected: term.cursor_row equals `1`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles newline character")
var term = Terminal.new(80, 25)
term.write_char("A")
term.write_char("\n")
expect(term.cursor_row).to_equal(1)
expect(term.cursor_col).to_equal(0)
```

</details>

### Terminal newline

#### moves cursor to next row

- moves cursor to next row
   - Expected: term.cursor_row equals `1`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves cursor to next row")
var term = Terminal.new(80, 25)
term.newline()
expect(term.cursor_row).to_equal(1)
expect(term.cursor_col).to_equal(0)
```

</details>

#### resets cursor_col to 0

- resets cursor_col to 0
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets cursor_col to 0")
var term = Terminal.new(80, 25)
term.write_char("X")
term.write_char("Y")
term.newline()
expect(term.cursor_col).to_equal(0)
```

</details>

#### scrolls when at last row

- scrolls when at last row
   - Expected: term.cursor_row equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scrolls when at last row")
var term = Terminal.new(80, 3)
term.cursor_row = 2
term.newline()
# After newline at last row, cursor stays at last row
expect(term.cursor_row).to_equal(2)
```

</details>

### Terminal scroll_up

#### shifts buffer up by one line

- shifts buffer up by one line
   - Expected: term.lines[0].chars[0].ch equals `B`
   - Expected: term.lines[1].chars[0].ch equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shifts buffer up by one line")
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

- adds blank line at bottom after scroll
   - Expected: term.lines[2].chars[0].ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds blank line at bottom after scroll")
var term = Terminal.new(10, 3)
term.lines[2].chars[0] = TerminalChar(ch: "X", fg: 7, bg: 0, bold: false)
term.scroll_up()
# Last line should be blank
expect(term.lines[2].chars[0].ch).to_equal(" ")
```

</details>

#### preserves line count after scroll

- preserves line count after scroll
   - Expected: term.lines.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves line count after scroll")
var term = Terminal.new(10, 5)
term.scroll_up()
expect(term.lines.len()).to_equal(5)
```

</details>

### Terminal clear

#### resets all lines to blank

- resets all lines to blank
   - Expected: term.lines[0].chars[0].ch equals ` `
   - Expected: term.lines[0].chars[1].ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets all lines to blank")
var term = Terminal.new(10, 3)
term.write_char("A")
term.write_char("B")
term.clear()
expect(term.lines[0].chars[0].ch).to_equal(" ")
expect(term.lines[0].chars[1].ch).to_equal(" ")
```

</details>

#### resets cursor to origin

- resets cursor to origin
   - Expected: term.cursor_row equals `0`
   - Expected: term.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets cursor to origin")
var term = Terminal.new(80, 25)
term.cursor_row = 10
term.cursor_col = 20
term.clear()
expect(term.cursor_row).to_equal(0)
expect(term.cursor_col).to_equal(0)
```

</details>

#### preserves number of lines

- preserves number of lines
   - Expected: term.lines.len() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves number of lines")
var term = Terminal.new(80, 25)
term.clear()
expect(term.lines.len()).to_equal(25)
```

</details>

### Terminal ANSI parsing

#### starts in Normal state

- starts in Normal state
   - Expected: term.ansi_state equals `AnsiState.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts in Normal state")
val term = Terminal.new(80, 25)
expect(term.ansi_state).to_equal(AnsiState.Normal)
```

</details>

#### AnsiState enum has Normal variant

- AnsiState enum has Normal variant
   - Expected: state equals `AnsiState.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AnsiState enum has Normal variant")
val state = AnsiState.Normal
expect(state).to_equal(AnsiState.Normal)
```

</details>

#### AnsiState enum has Escape variant

- AnsiState enum has Escape variant
   - Expected: state equals `AnsiState.Escape`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AnsiState enum has Escape variant")
val state = AnsiState.Escape
expect(state).to_equal(AnsiState.Escape)
```

</details>

#### AnsiState enum has Bracket variant

- AnsiState enum has Bracket variant
   - Expected: state equals `AnsiState.Bracket`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AnsiState enum has Bracket variant")
val state = AnsiState.Bracket
expect(state).to_equal(AnsiState.Bracket)
```

</details>

#### AnsiState enum has Param variant

- AnsiState enum has Param variant
   - Expected: state equals `AnsiState.Param`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AnsiState enum has Param variant")
val state = AnsiState.Param
expect(state).to_equal(AnsiState.Param)
```

</details>

### Terminal write_string

#### writes multiple characters

- writes multiple characters
   - Expected: term.cursor_col equals `5`
   - Expected: term.lines[0].chars[0].ch equals `H`
   - Expected: term.lines[0].chars[4].ch equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes multiple characters")
var term = Terminal.new(80, 25)
term.write_string("Hello")
expect(term.cursor_col).to_equal(5)
expect(term.lines[0].chars[0].ch).to_equal("H")
expect(term.lines[0].chars[4].ch).to_equal("o")
```

</details>

#### handles embedded newlines

- handles embedded newlines
   - Expected: term.lines[0].chars[0].ch equals `A`
   - Expected: term.lines[0].chars[1].ch equals `B`
   - Expected: term.lines[1].chars[0].ch equals `C`
   - Expected: term.lines[1].chars[1].ch equals `D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles embedded newlines")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1749777bf9b6b990fe7d0b9573ec0c2e093074646510d3ba30e4a80d9d22b9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1749777bf9b6b990fe7d0b9573ec0c2e093074646510d3ba30e4a80d9d22b9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1749777bf9b6b990fe7d0b9573ec0c2e093074646510d3ba30e4a80d9d22b9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/terminal/terminal_spec.spl
mirror: doc/06_spec/unit/os/apps/terminal/terminal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/terminal/terminal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/terminal/terminal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/terminal/terminal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/terminal/terminal_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with default values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/terminal/terminal_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with custom color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/terminal/terminal_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default_char returns space with white-on-black' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
