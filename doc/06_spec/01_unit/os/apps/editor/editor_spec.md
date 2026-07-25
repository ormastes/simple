# Text Editor Unit Tests

> Tests for TextEditor: construction, insert_char, delete_char, newline,

<!-- sdn-diagram:id=editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_spec -> std
editor_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/apps/editor/editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for TextEditor: construction, insert_char, delete_char, newline,
    mode transitions (Normal/Insert/Command), and cursor bounds.

    This describe block covers the EditorMode enum variants and the
    mode_name() formatter used in the status line.

## Scenarios

### EditorMode

#### has Normal variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = EditorMode.Normal
expect(mode).to_equal(EditorMode.Normal)
```

</details>

#### has Insert variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = EditorMode.Insert
expect(mode).to_equal(EditorMode.Insert)
```

</details>

#### has Command variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = EditorMode.Command
expect(mode).to_equal(EditorMode.Command)
```

</details>

#### mode_name returns NORMAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = mode_name(EditorMode.Normal)
expect(name).to_equal("NORMAL")
```

</details>

#### mode_name returns INSERT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = mode_name(EditorMode.Insert)
expect(name).to_equal("INSERT")
```

</details>

#### mode_name returns COMMAND

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = mode_name(EditorMode.Command)
expect(name).to_equal("COMMAND")
```

</details>

### TextEditor

#### when newly created

#### starts with one empty line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.lines.len()).to_equal(1)
expect(ed.lines[0]).to_equal("")
```

</details>

#### starts with cursor at row 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.cursor_row).to_equal(0)
```

</details>

#### starts with cursor at col 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.cursor_col).to_equal(0)
```

</details>

#### starts with scroll_row at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.scroll_row).to_equal(0)
```

</details>

#### starts with no file_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.file_path).to_be_nil
```

</details>

#### starts not modified

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.modified).to_equal(false)
```

</details>

#### starts in Normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.mode).to_equal(EditorMode.Normal)
```

</details>

#### starts with empty command_buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.command_buffer).to_equal("")
```

</details>

#### starts with empty yank_buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.yank_buffer.len()).to_equal(0)
```

</details>

#### starts with Ready status message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.status_message).to_equal("Ready")
```

</details>

#### has default visible_rows of 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.visible_rows).to_equal(20)
```

</details>

#### has default visible_cols of 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.visible_cols).to_equal(80)
```

</details>

#### has nil vfs by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ed = TextEditor.new()
expect(ed.vfs).to_be_nil
```

</details>

### TextEditor insert_char

#### adds character at cursor position

1. var ed = TextEditor new
2. ed insert char


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
expect(ed.lines[0]).to_contain("A")
```

</details>

#### advances cursor after insert

1. var ed = TextEditor new
2. ed insert char
   - Expected: ed.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
expect(ed.cursor_col).to_equal(1)
```

</details>

#### inserts multiple characters sequentially

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
   - Expected: ed.cursor_col equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("H")
ed.insert_char("i")
expect(ed.cursor_col).to_equal(2)
expect(ed.lines[0]).to_start_with("Hi")
```

</details>

#### marks document as modified

1. var ed = TextEditor new
2. ed insert char
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
expect(ed.modified).to_equal(true)
```

</details>

#### inserts at middle of existing text

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed insert char
   - Expected: ed.lines[0] equals `ABC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed delete char


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed insert char
3. ed delete char
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed delete char before
   - Expected: ed.cursor_col equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("A")
ed.insert_char("B")
ed.delete_char_before()
expect(ed.cursor_col).to_equal(1)
```

</details>

#### does nothing when cursor at column 0 row 0

1. var ed = TextEditor new
2. ed delete char before
   - Expected: ed.cursor_col equals `0`
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.delete_char_before()
expect(ed.cursor_col).to_equal(0)
expect(ed.cursor_row).to_equal(0)
```

</details>

#### joins with previous line when at column 0

1. var ed = TextEditor new
2. ed insert char
3. ed newline
4. ed insert char
5. ed delete char before
   - Expected: ed.cursor_row equals `0`
   - Expected: ed.lines.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed newline
   - Expected: ed.lines.len() equals `2`
   - Expected: ed.lines[0] equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed insert char
3. ed newline
   - Expected: ed.cursor_row equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.newline()
expect(ed.cursor_row).to_equal(1)
```

</details>

#### resets cursor col to 0

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed newline
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.insert_char("Y")
ed.newline()
expect(ed.cursor_col).to_equal(0)
```

</details>

#### marks document as modified

1. var ed = TextEditor new
2. ed newline
   - Expected: ed.modified is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.newline()
expect(ed.modified).to_equal(true)
```

</details>

#### creates empty line when at end of text

1. var ed = TextEditor new
2. ed insert char
3. ed newline
   - Expected: ed.lines.len() equals `2`
   - Expected: ed.lines[1] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.handle_normal_key("i")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### sets INSERT status message

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.status_message equals `-- INSERT --`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.handle_normal_key("i")
expect(ed.status_message).to_equal("-- INSERT --")
```

</details>

#### switches to Insert on 'a' key (append)

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.handle_normal_key("a")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### switches to Insert on 'o' key (open below)

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.mode equals `EditorMode.Insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.handle_normal_key("o")
expect(ed.mode).to_equal(EditorMode.Insert)
```

</details>

#### Insert to Normal

#### switches to Normal on escape

1. var ed = TextEditor new
2. ed handle insert key
   - Expected: ed.mode equals `EditorMode.Normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("escape")
expect(ed.mode).to_equal(EditorMode.Normal)
```

</details>

#### clears status message on escape

1. var ed = TextEditor new
2. ed handle insert key
   - Expected: ed.status_message equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.status_message = "-- INSERT --"
ed.handle_insert_key("escape")
expect(ed.status_message).to_equal("")
```

</details>

#### Insert mode key handling

#### inserts character on regular key

1. var ed = TextEditor new
2. ed handle insert key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("A")
expect(ed.lines[0]).to_contain("A")
```

</details>

#### handles enter key

1. var ed = TextEditor new
2. ed handle insert key
   - Expected: ed.lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.handle_insert_key("enter")
expect(ed.lines.len()).to_equal(2)
```

</details>

#### handles backspace key

1. var ed = TextEditor new
2. ed insert char
3. ed handle insert key
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.mode = EditorMode.Insert
ed.insert_char("X")
ed.handle_insert_key("backspace")
expect(ed.cursor_col).to_equal(0)
```

</details>

### TextEditor cursor bounds

#### h does not go below col 0

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.cursor_col = 0
ed.handle_normal_key("h")
expect(ed.cursor_col).to_equal(0)
```

</details>

#### k does not go below row 0

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
ed.cursor_row = 0
ed.handle_normal_key("k")
expect(ed.cursor_row).to_equal(0)
```

</details>

#### j does not go past last line

1. var ed = TextEditor new
2. ed handle normal key
   - Expected: ed.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ed = TextEditor.new()
# Only 1 line, so j should not advance
ed.handle_normal_key("j")
expect(ed.cursor_row).to_equal(0)
```

</details>

#### 0 moves to start of line

1. var ed = TextEditor new
2. ed insert char
3. ed insert char
4. ed insert char
5. ed handle normal key
   - Expected: ed.cursor_col equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
