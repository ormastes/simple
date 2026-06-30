# Editor Buffer Specification

> <details>

<!-- sdn-diagram:id=editor_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_buffer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Buffer Specification

## Scenarios

### editor types — core structs

#### defines EditorBufferId with value field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("class EditorBufferId:")).to_equal(true)
expect(src.contains("value: i64")).to_equal(true)
```

</details>

#### defines EditorMode enum with Normal/Insert/Command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("enum EditorMode:")).to_equal(true)
expect(src.contains("Normal")).to_equal(true)
expect(src.contains("Insert")).to_equal(true)
expect(src.contains("Command")).to_equal(true)
```

</details>

#### defines EditorCursor with row and col

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("struct EditorCursor:")).to_equal(true)
expect(src.contains("row: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
```

</details>

#### defines EditorViewport with top_row, width, height

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("struct EditorViewport:")).to_equal(true)
expect(src.contains("top_row: i64")).to_equal(true)
expect(src.contains("width: i64")).to_equal(true)
expect(src.contains("height: i64")).to_equal(true)
```

</details>

#### defines EditCommand with name, payload, count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("struct EditCommand:")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("payload: text")).to_equal(true)
expect(src.contains("count: i64")).to_equal(true)
```

</details>

#### defines EditResult with ok, message, quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("struct EditResult:")).to_equal(true)
expect(src.contains("ok: bool")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("quit: bool")).to_equal(true)
```

</details>

#### provides editor_clamp utility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/types.spl")
expect(src.contains("fn editor_clamp(value: i64, low: i64, high: i64) -> i64")).to_equal(true)
```

</details>

### editor piece table — structure

#### defines PieceTable with content storage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/piece_table.spl")
expect(src.contains("class PieceTable:")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
```

</details>

#### defines PieceTable class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/piece_table.spl")
expect(src.contains("class PieceTable:")).to_equal(true)
expect(src.contains("content: text")).to_equal(true)
```

</details>

#### has new static constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/piece_table.spl")
expect(src.contains("static fn new(initial: text) -> PieceTable")).to_equal(true)
```

</details>

#### has len, to_text, insert, delete methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/piece_table.spl")
expect(src.contains("fn to_text() -> text")).to_equal(true)
expect(src.contains("me insert(line: i64, col: i64, text_to_insert: text)")).to_equal(true)
expect(src.contains("me delete(line: i64, col: i64, count: i64)")).to_equal(true)
```

</details>

#### has line_count, line_at, line_starts methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/piece_table.spl")
expect(src.contains("fn line_count() -> i64")).to_equal(true)
expect(src.contains("fn line_at(n: i64) -> text")).to_equal(true)
expect(src.contains("fn to_text() -> text")).to_equal(true)
```

</details>

### editor piece table — internals

#### inserts deletes and reads lines

1. var table = PieceTable new
2. table insert
   - Expected: table.line_at(0) equals `alpha!`
3. table delete
   - Expected: table.line_at(0) equals `alpha`
   - Expected: table.line_count() equals `2`
   - Expected: table.to_text() equals `alpha\nbeta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = PieceTable.new("alpha\nbeta")
table.insert(0, 5, "!")
expect(table.line_at(0)).to_equal("alpha!")
table.delete(0, 5, 1)
expect(table.line_at(0)).to_equal("alpha")
expect(table.line_count()).to_equal(2)
expect(table.to_text()).to_equal("alpha\nbeta")
```

</details>

### editor undo — stack operations

#### defines UndoEntry with content, cursor_row, cursor_col

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/undo.spl")
expect(src.contains("struct BufferUndoEntry:")).to_equal(true)
expect(src.contains("before: text")).to_equal(true)
expect(src.contains("after: text")).to_equal(true)
expect(src.contains("cursor_line: i64")).to_equal(true)
expect(src.contains("cursor_col: i64")).to_equal(true)
```

</details>

#### defines UndoStack class with undo and redo lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/undo.spl")
expect(src.contains("class BufferUndoStack:")).to_equal(true)
expect(src.contains("past: [BufferUndoEntry]")).to_equal(true)
expect(src.contains("future: [BufferUndoEntry]")).to_equal(true)
expect(src.contains("max_size: i64")).to_equal(true)
```

</details>

#### has push, can_undo, can_redo, undo, redo methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/undo.spl")
expect(src.contains("me record(before: text, after: text, cursor_line: i64, cursor_col: i64)")).to_equal(true)
expect(src.contains("fn can_undo() -> bool")).to_equal(true)
expect(src.contains("fn can_redo() -> bool")).to_equal(true)
expect(src.contains("me undo() -> Option<BufferUndoEntry>")).to_equal(true)
expect(src.contains("me redo() -> Option<BufferUndoEntry>")).to_equal(true)
```

</details>

#### clears redo on push

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/undo.spl")
expect(src.contains("me.future = []")).to_equal(true)
```

</details>

#### trims undo stack beyond max_depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/undo.spl")
expect(src.contains("me.past.len() > me.max_size")).to_equal(true)
expect(src.contains("me.past = trimmed")).to_equal(true)
```

</details>

### editor buffer — wrapper

#### defines EditorBuffer class with piece_table and undo_stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("class EditorBuffer:")).to_equal(true)
expect(src.contains("table: PieceTable")).to_equal(true)
expect(src.contains("dirty: bool")).to_equal(true)
```

</details>

#### has from_text and from_file constructors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("static fn from_text(id: EditorBufferId, content: text) -> EditorBuffer")).to_equal(true)
expect(src.contains("static fn new() -> EditorBuffer")).to_equal(true)
```

</details>

#### has insert_at_cursor and delete_before_cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me insert_at_cursor(content: text)")).to_equal(true)
expect(src.contains("me delete_before_cursor()")).to_equal(true)
expect(src.contains("me delete_at_cursor()")).to_equal(true)
```

</details>

#### has cursor movement methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me move_cursor(row: i64, col: i64)")).to_equal(true)
expect(src.contains("me move_relative(line_delta: i64, col_delta: i64)")).to_equal(true)
expect(src.contains("me move_to_line_start()")).to_equal(true)
expect(src.contains("me move_to_line_end()")).to_equal(true)
```

</details>

#### has undo and redo delegating to UndoStack

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me undo()")).to_equal(true)
expect(src.contains("me redo()")).to_equal(true)
expect(src.contains("undo_available")).to_equal(true)
expect(src.contains("undo_text")).to_equal(true)
```

</details>

#### has save and save_as for file persistence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me save() -> bool")).to_equal(true)
expect(src.contains("me save_as(path: text) -> bool")).to_equal(true)
expect(src.contains("rt_file_write_text")).to_equal(true)
```

</details>

#### serializes and restores folded ranges

1. var buffer = EditorBuffer from text
2. buffer fold range
   - Expected: buffer.fold_state() equals `0-1`
3. var restored = EditorBuffer from text
4. restored move cursor
5. restored restore fold state
   - Expected: restored.has_fold_range(0, 1) is true
   - Expected: restored.cursor_row equals `0`
   - Expected: restored.is_line_folded(1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "head\nbody\nnext\n")
buffer.fold_range(0, 1)
expect(buffer.fold_state()).to_equal("0-1")

var restored = EditorBuffer.from_text(EditorBufferId(value: 2), "head\nbody\nnext\n")
restored.move_cursor(1, 0)
restored.restore_fold_state(buffer.fold_state())
expect(restored.has_fold_range(0, 1)).to_equal(true)
expect(restored.cursor_row).to_equal(0)
expect(restored.is_line_folded(1)).to_equal(true)
```

</details>

#### renders folded header markers

1. var buffer = EditorBuffer from text
2. buffer fold range
   - Expected: buffer.folded_end_line_for_header(0) equals `1`
   - Expected: buffer.folded_end_line_for_header(2) equals `-1`
   - Expected: buffer.line_with_fold_marker(0) equals `head  [+1 folded | za]`
   - Expected: buffer.line_with_fold_marker(2) equals `next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "head\nbody\nnext\n")
buffer.fold_range(0, 1)
expect(buffer.folded_end_line_for_header(0)).to_equal(1)
expect(buffer.folded_end_line_for_header(2)).to_equal(-1)
expect(buffer.line_with_fold_marker(0)).to_equal("head  [+1 folded | za]")
expect(buffer.line_with_fold_marker(2)).to_equal("next")
```

</details>

#### pushes undo snapshot before mutations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me.push_undo_snapshot()")).to_equal(true)
```

</details>

#### tracks dirty flag on edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me.dirty = true")).to_equal(true)
expect(src.contains("me.dirty = false")).to_equal(true)
```

</details>

#### ensures cursor visible within viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/buffer.spl")
expect(src.contains("me ensure_cursor_visible()")).to_equal(true)
expect(src.contains("me.viewport.top_row = me.cursor_row")).to_equal(true)
```

</details>

#### replaces and deletes active selection ranges

1. var buffer = EditorBuffer from text
2. buffer set selection range
3. buffer insert at cursor
   - Expected: buffer.to_text() equals `alpha B\ngamma\n`
   - Expected: buffer.cursor_row equals `0`
   - Expected: buffer.cursor_col equals `7`
   - Expected: buffer.selection_range.active is false
4. buffer set selection range
5. buffer delete at cursor
   - Expected: buffer.to_text() equals ` B\ngamma\n`
   - Expected: buffer.cursor_row equals `0`
   - Expected: buffer.cursor_col equals `0`
6. buffer undo
   - Expected: buffer.to_text() equals `alpha B\ngamma\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), "alpha beta\ngamma\n")
buffer.set_selection_range(0, 6, 0, 10)
buffer.insert_at_cursor("B")
expect(buffer.to_text()).to_equal("alpha B\ngamma\n")
expect(buffer.cursor_row).to_equal(0)
expect(buffer.cursor_col).to_equal(7)
expect(buffer.selection_range.active).to_equal(false)

buffer.set_selection_range(0, 0, 0, 5)
buffer.delete_at_cursor()
expect(buffer.to_text()).to_equal(" B\ngamma\n")
expect(buffer.cursor_row).to_equal(0)
expect(buffer.cursor_col).to_equal(0)

buffer.undo()
expect(buffer.to_text()).to_equal("alpha B\ngamma\n")
```

</details>

#### stores renders and edits multiple active selection ranges

1. var buffer = EditorBuffer from text
2. buffer set selection range
3. buffer add selection range
   - Expected: buffer.selection_range_count() equals `2`
   - Expected: buffer.line_has_selection(0) is true
   - Expected: buffer.line_has_selection(1) is true
   - Expected: buffer.position_selected(0, 1) is true
   - Expected: buffer.position_selected(1, 1) is true
   - Expected: buffer.position_selected(0, 4) is false
4. buffer insert at cursor
   - Expected: buffer.to_text() equals `X two\nX blue\n`
   - Expected: buffer.selection_range_count() equals `0`
   - Expected: buffer.cursor_row equals `0`
   - Expected: buffer.cursor_col equals `1`
5. buffer set selection range
6. buffer add selection range
7. buffer delete at cursor
   - Expected: buffer.to_text() equals ` two\n blue\n`
   - Expected: buffer.selection_range_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = EditorBuffer.from_text(EditorBufferId(value: 2), "one two\nred blue\n")
buffer.set_selection_range(0, 0, 0, 3)
buffer.add_selection_range(1, 0, 1, 3)
expect(buffer.selection_range_count()).to_equal(2)
expect(buffer.line_has_selection(0)).to_equal(true)
expect(buffer.line_has_selection(1)).to_equal(true)
expect(buffer.position_selected(0, 1)).to_equal(true)
expect(buffer.position_selected(1, 1)).to_equal(true)
expect(buffer.position_selected(0, 4)).to_equal(false)

buffer.insert_at_cursor("X")
expect(buffer.to_text()).to_equal("X two\nX blue\n")
expect(buffer.selection_range_count()).to_equal(0)
expect(buffer.cursor_row).to_equal(0)
expect(buffer.cursor_col).to_equal(1)

buffer.set_selection_range(0, 0, 0, 1)
buffer.add_selection_range(1, 0, 1, 1)
buffer.delete_at_cursor()
expect(buffer.to_text()).to_equal(" two\n blue\n")
expect(buffer.selection_range_count()).to_equal(0)
```

</details>

### editor commands — dispatch

#### defines editor_dispatch function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("fn editor_dispatch(buffer: EditorBuffer, cmd: EditCommand) -> EditResult")).to_equal(true)
```

</details>

#### handles movement commands (left/right/up/down)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"move-left\"")).to_equal(true)
expect(src.contains("\"move-right\"")).to_equal(true)
expect(src.contains("\"move-up\"")).to_equal(true)
expect(src.contains("\"move-down\"")).to_equal(true)
```

</details>

#### handles editing commands (insert/backspace/delete)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"insert-text\"")).to_equal(true)
expect(src.contains("\"backspace\"")).to_equal(true)
expect(src.contains("\"delete\"")).to_equal(true)
expect(src.contains("\"newline\"")).to_equal(true)
```

</details>

#### handles undo and redo commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"undo\"")).to_equal(true)
expect(src.contains("\"redo\"")).to_equal(true)
```

</details>

#### handles save and quit commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"save\"")).to_equal(true)
expect(src.contains("\"quit\"")).to_equal(true)
```

</details>

#### parses commandline inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("fn editor_parse_commandline(line: text) -> EditCommand")).to_equal(true)
expect(src.contains("trimmed == \"w\"")).to_equal(true)
expect(src.contains("trimmed == \"q\"")).to_equal(true)
expect(src.contains("trimmed == \"q!\"")).to_equal(true)
```

</details>

### editor TUI shell — rendering

#### defines editor_tui_run entry point with EditSession

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("fn editor_tui_run(session: EditSession)")).to_equal(true)
```

</details>

#### enters and exits alt screen and raw mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("terminal_enter_alt_screen()")).to_equal(true)
expect(src.contains("terminal_exit_alt_screen()")).to_equal(true)
expect(src.contains("terminal_enter_raw_mode()")).to_equal(true)
expect(src.contains("terminal_exit_raw_mode()")).to_equal(true)
```

</details>

#### renders line numbers and editor content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("buffer.line_with_fold_marker(file_row)")).to_equal(true)
expect(src.contains("str(file_row + 1)")).to_equal(true)
```

</details>

#### has tab bar rendering function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_tab_bar(session: EditSession, width: i64)")).to_equal(true)
```

</details>

#### has file tree rendering function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_file_tree(file_tree: FileTreeState, start_row: i64, height: i64, width: i64, focused: bool)")).to_equal(true)
```

</details>

#### has file tree key handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_file_tree_key(key: text) -> EditorAction")).to_equal(true)
```

</details>

#### supports file tree toggle with Ctrl+B

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("file_tree_visible")).to_equal(true)
expect(src.contains("focus_panel")).to_equal(true)
expect(src.contains("toggle_file_tree")).to_equal(true)
```

</details>

#### renders status bar with mode, path, position

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("editor_mode_name(ctrl.session.mode)")).to_equal(true)
expect(src.contains("buffer.path")).to_equal(true)
expect(src.contains("buffer.cursor_row + 1")).to_equal(true)
```

</details>

#### handles normal mode keys (h/j/k/l/i/q)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("fn ctrl_handle_normal_key(buffer: EditorBuffer, key: text) -> NormalKeyResult")).to_equal(true)
expect(src.contains("key == \"h\"")).to_equal(true)
expect(src.contains("key == \"j\"")).to_equal(true)
expect(src.contains("key == \"i\"")).to_equal(true)
```

</details>

#### handles insert mode with ESC to exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_insert_key(key: text) -> EditorAction")).to_equal(true)
expect(src.contains("exit_insert = true")).to_equal(true)
```

</details>

#### handles command mode with enter to execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_command_key(key: text) -> EditorAction")).to_equal(true)
expect(src.contains("ctrl_dispatch_command_key(me, key)")).to_equal(true)
```

</details>

### editor main — entry point

#### defines main function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/main.spl")
expect(src.contains("fn main()")).to_equal(true)
```

</details>

#### reads command line args for file paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/main.spl")
expect(src.contains("get_cli_args()")).to_equal(true)
expect(src.contains("editor_launch_file_count(args)")).to_equal(true)
```

</details>

#### creates EditSession and opens empty if no args

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/main.spl")
expect(src.contains("editor_launch_mode(args)")).to_equal(true)
expect(src.contains("Ready for ")).to_equal(true)
expect(src.contains("editor startup")).to_equal(true)
```

</details>

#### calls editor_tui_run with session

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/main.spl")
expect(src.contains("editor_tui_run(session)")).to_equal(true)
```

</details>

### editor commands — session dispatch

#### defines editor_dispatch_session for session-level commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("fn editor_dispatch_session(session: EditSession, cmd: EditCommand) -> EditResult")).to_equal(true)
```

</details>

#### handles open-file command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"open-file\"")).to_equal(true)
expect(src.contains("session.open_file(cmd.payload)")).to_equal(true)
```

</details>

#### handles tab navigation commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"tab-next\"")).to_equal(true)
expect(src.contains("\"tab-prev\"")).to_equal(true)
expect(src.contains("\"tab-close\"")).to_equal(true)
```

</details>

#### handles split and focus commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"split\"")).to_equal(true)
expect(src.contains("\"focus-next\"")).to_equal(true)
expect(src.contains("\"focus-prev\"")).to_equal(true)
```

</details>

#### falls through to buffer dispatch for unknown session commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("editor_dispatch(buffer, cmd)")).to_equal(true)
```

</details>

#### parses :e and :edit for open-file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("starts_with(\"e \")")).to_equal(true)
expect(src.contains("starts_with(\"edit \")")).to_equal(true)
```

</details>

#### parses :bn/:bp/:bd for tab commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"bn\"")).to_equal(true)
expect(src.contains("trimmed == \"bp\"")).to_equal(true)
expect(src.contains("trimmed == \"bd\"")).to_equal(true)
```

</details>

#### parses :vs/:split for split command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("trimmed == \"vs\"")).to_equal(true)
expect(src.contains("trimmed == \"split\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor types — core structs
- editor piece table — structure
- editor piece table — internals
- editor undo — stack operations
- editor buffer — wrapper
- editor commands — dispatch
- editor TUI shell — rendering
- editor main — entry point
- editor commands — session dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
