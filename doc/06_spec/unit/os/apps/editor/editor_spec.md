# Text Editor Unit Tests

> Tests for TextEditor: construction, insert_char, delete_char, newline,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Editor Unit Tests

Tests for TextEditor: construction, insert_char, delete_char, newline,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/editor/editor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for TextEditor: construction, insert_char, delete_char, newline,
    mode transitions (Normal/Insert/Command), and cursor bounds.

    This describe block covers the EditorMode enum variants and the
    mode_name() formatter used in the status line.

## Scenarios

### EditorMode

#### has Normal variant

- has Normal variant
   - Expected: mode equals `EditorMode.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Normal variant")
"""EditorMode.Normal exists and equals itself."""
val mode = EditorMode.Normal
expect(mode).to_equal(EditorMode.Normal)
```

</details>

#### has Insert variant

- has Insert variant
   - Expected: mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Insert variant")
val mode = EditorMode.Insert
expect(mode).to_equal(EditorMode.Insert)
```

</details>

#### has Command variant

- has Command variant
   - Expected: mode equals `EditorMode.Command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Command variant")
val mode = EditorMode.Command
expect(mode).to_equal(EditorMode.Command)
```

</details>

#### mode_name returns NORMAL

- mode_name returns NORMAL
   - Expected: name equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mode_name returns NORMAL")
val name = mode_name(EditorMode.Normal)
expect(name).to_equal("NORMAL")
```

</details>

#### mode_name returns INSERT

- mode_name returns INSERT
   - Expected: name equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mode_name returns INSERT")
val name = mode_name(EditorMode.Insert)
expect(name).to_equal("INSERT")
```

</details>

#### mode_name returns COMMAND

- mode_name returns COMMAND
   - Expected: name equals `COMMAND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mode_name returns COMMAND")
val name = mode_name(EditorMode.Command)
expect(name).to_equal("COMMAND")
```

</details>

### TextEditor

#### when newly created

#### starts with one empty line

- starts with one empty line
   - Expected: ed.lines.len() equals `1`
   - Expected: ed.lines[0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with one empty line")
val ed = TextEditor.new()
expect(ed.lines.len()).to_equal(1)
expect(ed.lines[0]).to_equal("")
```

</details>

#### starts with cursor at row 0

- starts with cursor at row 0
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with cursor at row 0")
val ed = TextEditor.new()
expect(ed.cursor_row).to_equal(0)
```

</details>

#### starts with cursor at col 0

- starts with cursor at col 0
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with cursor at col 0")
val ed = TextEditor.new()
expect(ed.cursor_col).to_equal(0)
```

</details>

#### starts with scroll_row at 0

- starts with scroll_row at 0
   - Expected: ed.scroll_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with scroll_row at 0")
val ed = TextEditor.new()
expect(ed.scroll_row).to_equal(0)
```

</details>

#### starts with no file_path

- starts with no file_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with no file_path")
val ed = TextEditor.new()
expect(ed.file_path).to_be_nil
```

</details>

#### starts not modified

- starts not modified
   - Expected: ed.modified is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts not modified")
val ed = TextEditor.new()
expect(ed.modified).to_equal(false)
```

</details>

#### starts in Normal mode

- starts in Normal mode
   - Expected: ed.mode equals `EditorMode.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts in Normal mode")
val ed = TextEditor.new()
expect(ed.mode).to_equal(EditorMode.Normal)
```

</details>

#### starts with empty command_buffer

- starts with empty command_buffer
   - Expected: ed.command_buffer equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty command_buffer")
val ed = TextEditor.new()
expect(ed.command_buffer).to_equal("")
```

</details>

#### starts with empty yank_buffer

- starts with empty yank_buffer
   - Expected: ed.yank_buffer.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty yank_buffer")
val ed = TextEditor.new()
expect(ed.yank_buffer.len()).to_equal(0)
```

</details>

#### starts with Ready status message

- starts with Ready status message
   - Expected: ed.status_message equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with Ready status message")
val ed = TextEditor.new()
expect(ed.status_message).to_equal("Ready")
```

</details>

#### has default visible_rows of 20

- has default visible_rows of 20
   - Expected: ed.visible_rows equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has default visible_rows of 20")
val ed = TextEditor.new()
expect(ed.visible_rows).to_equal(20)
```

</details>

#### has default visible_cols of 80

- has default visible_cols of 80
   - Expected: ed.visible_cols equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has default visible_cols of 80")
val ed = TextEditor.new()
expect(ed.visible_cols).to_equal(80)
```

</details>

#### has nil vfs by default

- has nil vfs by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has nil vfs by default")
val ed = TextEditor.new()
expect(ed.vfs).to_be_nil
```

</details>

### TextEditor insert_char

#### adds character at cursor position

- adds character at cursor position


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds character at cursor position")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
expect(ed.lines[0]).to_contain("A")
```

</details>

#### advances cursor after insert

- advances cursor after insert
   - Expected: ed.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances cursor after insert")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
expect(ed.cursor_col).to_equal(1)
```

</details>

#### inserts multiple characters sequentially

- inserts multiple characters sequentially
   - Expected: ed.cursor_col equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts multiple characters sequentially")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("H")
ed.insert_char("i")
expect(ed.cursor_col).to_equal(2)
expect(ed.lines[0]).to_start_with("Hi")
```

</details>

#### marks document as modified

- marks document as modified
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks document as modified")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
expect(ed.modified).to_equal(true)
```

</details>

#### inserts at middle of existing text

- inserts at middle of existing text
   - Expected: ed.lines[0] equals `ABC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts at middle of existing text")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("C")
ed.cursor_col = 1
ed.insert_char("B")
expect(ed.lines[0]).to_equal("ABC")
```

</details>

### TextEditor delete_char

#### removes character at cursor

- removes character at cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes character at cursor")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("B")
ed.cursor_col = 0
ed.delete_char()
expect(ed.lines[0]).to_start_with("B")
```

</details>

#### marks document as modified

- marks document as modified
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks document as modified")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.cursor_col = 0
ed.delete_char()
expect(ed.modified).to_equal(true)
```

</details>

### TextEditor delete_char_before

#### deletes character before cursor (backspace)

- deletes character before cursor (backspace)
   - Expected: ed.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes character before cursor (backspace)")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("B")
ed.delete_char_before()
expect(ed.cursor_col).to_equal(1)
```

</details>

#### does nothing when cursor at column 0 row 0

- does nothing when cursor at column 0 row 0
   - Expected: ed.cursor_col equals `0`
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does nothing when cursor at column 0 row 0")
var ed = TextEditor.new()
ed.delete_char_before()
expect(ed.cursor_col).to_equal(0)
expect(ed.cursor_row).to_equal(0)
```

</details>

#### joins with previous line when at column 0

- joins with previous line when at column 0
   - Expected: ed.cursor_row equals `0`
   - Expected: ed.lines.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins with previous line when at column 0")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.newline()
ed.insert_char("B")
ed.cursor_col = 0
ed.delete_char_before()
expect(ed.cursor_row).to_equal(0)
expect(ed.lines.len()).to_equal(1)
```

</details>

### TextEditor newline

#### splits line at cursor

- splits line at cursor
   - Expected: ed.lines.len() equals `2`
   - Expected: ed.lines[0] equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits line at cursor")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("B")
ed.cursor_col = 1
ed.newline()
expect(ed.lines.len()).to_equal(2)
expect(ed.lines[0]).to_equal("A")
expect(ed.lines[1]).to_start_with("B")
```

</details>

#### moves cursor to next row

- moves cursor to next row
   - Expected: ed.cursor_row equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves cursor to next row")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.newline()
expect(ed.cursor_row).to_equal(1)
```

</details>

#### resets cursor col to 0

- resets cursor col to 0
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets cursor col to 0")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.insert_char("Y")
ed.newline()
expect(ed.cursor_col).to_equal(0)
```

</details>

#### marks document as modified

- marks document as modified
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks document as modified")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.newline()
expect(ed.modified).to_equal(true)
```

</details>

#### creates empty line when at end of text

- creates empty line when at end of text
   - Expected: ed.lines.len() equals `2`
   - Expected: ed.lines[1] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty line when at end of text")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("Z")
ed.newline()
expect(ed.lines.len()).to_equal(2)
expect(ed.lines[1]).to_equal("")
```

</details>

### TextEditor mode transitions

#### Normal to Insert

#### switches to Insert on 'i' key

- switches to Insert on 'i' key
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to Insert on 'i' key")
var ed = TextEditor.new()
ed.handle_normal_key("i")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### sets INSERT status message

- sets INSERT status message
   - Expected: ed.status_message equals `-- INSERT --`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets INSERT status message")
var ed = TextEditor.new()
ed.handle_normal_key("i")
expect(ed.status_message).to_equal("-- INSERT --")
```

</details>

#### switches to Insert on 'a' key (append)

- switches to Insert on 'a' key (append)
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to Insert on 'a' key (append)")
var ed = TextEditor.new()
ed.handle_normal_key("a")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### switches to Insert on 'o' key (open below)

- switches to Insert on 'o' key (open below)
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to Insert on 'o' key (open below)")
var ed = TextEditor.new()
ed.handle_normal_key("o")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### Insert to Normal

#### switches to Normal on escape

- switches to Normal on escape
   - Expected: ed.mode equals `EditorMode.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to Normal on escape")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("escape")
expect(ed.mode).to_equal(EditorMode.Normal)
```

</details>

#### clears status message on escape

- clears status message on escape
   - Expected: ed.status_message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears status message on escape")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.status_message = "-- INSERT --"
ed.handle_insert_key("escape")
expect(ed.status_message).to_equal("")
```

</details>

#### Insert mode key handling

#### inserts character on regular key

- inserts character on regular key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts character on regular key")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("A")
expect(ed.lines[0]).to_contain("A")
```

</details>

#### handles enter key

- handles enter key
   - Expected: ed.lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles enter key")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("enter")
expect(ed.lines.len()).to_equal(2)
```

</details>

#### handles backspace key

- handles backspace key
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles backspace key")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.handle_insert_key("backspace")
expect(ed.cursor_col).to_equal(0)
```

</details>

### TextEditor cursor bounds

#### h does not go below col 0

- h does not go below col 0
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("h does not go below col 0")
var ed = TextEditor.new()
ed.cursor_col = 0
ed.handle_normal_key("h")
expect(ed.cursor_col).to_equal(0)
```

</details>

#### k does not go below row 0

- k does not go below row 0
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("k does not go below row 0")
var ed = TextEditor.new()
ed.cursor_row = 0
ed.handle_normal_key("k")
expect(ed.cursor_row).to_equal(0)
```

</details>

#### j does not go past last line

- j does not go past last line
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("j does not go past last line")
var ed = TextEditor.new()
# Only 1 line, so j should not advance
ed.handle_normal_key("j")
expect(ed.cursor_row).to_equal(0)
```

</details>

#### 0 moves to start of line

- 0 moves to start of line
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 moves to start of line")
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("B")
ed.insert_char("C")
ed.mode = EditorMode.Normal
ed.handle_normal_key("0")
expect(ed.cursor_col).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
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

- Canonical SPipe generation for source `2eca13d53a56a672c605826c839ca96e6dc948b7be6c61ffd45a202cc768bcd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2eca13d53a56a672c605826c839ca96e6dc948b7be6c61ffd45a202cc768bcd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2eca13d53a56a672c605826c839ca96e6dc948b7be6c61ffd45a202cc768bcd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/apps/editor/editor_spec.spl
mirror: doc/06_spec/unit/os/apps/editor/editor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/editor/editor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/editor/editor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/editor/editor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/apps/editor/editor_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Normal variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/editor/editor_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Insert variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/editor/editor_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Command variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
