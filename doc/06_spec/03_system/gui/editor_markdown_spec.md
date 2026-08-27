# Editor Markdown Specification

> Tests covering editor block model — structure, editor block model — activation, editor block model — block kinds, editor markdown renderer — output, editor syntax highlight — tokens, editor block model — cursor helpers, editor markdown renderer — viewport, editor syntax highlight — dispatcher, editor markdown wiring — controller, editor markdown wiring — document, editor markdown wiring — commands, editor markdown wiring — tui shell, editor markdown wiring — md_dispatch glue, editor markdown wiring — gui shell, editor markdown property diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 83 | 83 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Markdown Specification

## Scenarios

### editor block model — structure

#### defines RenderBlock with id, kind, from_line, to_line

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines RenderBlock with id, kind, from_line, to_line
   - Expected: src contains `struct RenderBlock:`
   - Expected: src contains `id: i64`
   - Expected: src contains `kind: text`
   - Expected: src contains `from_line: i64`
   - Expected: src contains `to_line: i64`
   - Expected: src contains `rendered_lines: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines RenderBlock with id, kind, from_line, to_line")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("struct RenderBlock:")).to_equal(true)
expect(src.contains("id: i64")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("from_line: i64")).to_equal(true)
expect(src.contains("to_line: i64")).to_equal(true)
expect(src.contains("rendered_lines: [text]")).to_equal(true)
```

</details>

#### defines BlockModel class with blocks and active_block

- defines BlockModel class with blocks and active_block
   - Expected: src contains `class BlockModel:`
   - Expected: src contains `blocks: [RenderBlock]`
   - Expected: src contains `active_block: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines BlockModel class with blocks and active_block")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("class BlockModel:")).to_equal(true)
expect(src.contains("blocks: [RenderBlock]")).to_equal(true)
expect(src.contains("active_block: i64")).to_equal(true)
```

</details>

#### has from_markdown static constructor

- has from_markdown static constructor
   - Expected: src contains `static fn from_markdown(content: text) -> BlockModel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has from_markdown static constructor")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("static fn from_markdown(content: text) -> BlockModel")).to_equal(true)
```

</details>

#### has block_count, block_at, block_for_line

- has block_count, block_at, block_for_line
   - Expected: src contains `fn block_count() -> i64`
   - Expected: src contains `fn block_at(index: i64) -> RenderBlock`
   - Expected: src contains `fn block_for_line(line: i64) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has block_count, block_at, block_for_line")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn block_count() -> i64")).to_equal(true)
expect(src.contains("fn block_at(index: i64) -> RenderBlock")).to_equal(true)
expect(src.contains("fn block_for_line(line: i64) -> i64")).to_equal(true)
```

</details>

### editor block model — activation

#### has activate_block and deactivate_block

- has activate_block and deactivate_block
   - Expected: src contains `me activate_block(index: i64)`
   - Expected: src contains `me deactivate_block()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has activate_block and deactivate_block")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("me activate_block(index: i64)")).to_equal(true)
expect(src.contains("me deactivate_block()")).to_equal(true)
```

</details>

#### has is_active to check block state

- has is_active to check block state
   - Expected: src contains `fn is_active(index: i64) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has is_active to check block state")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn is_active(index: i64) -> bool")).to_equal(true)
```

</details>

#### has rebuild to reparse content

- has rebuild to reparse content
   - Expected: src contains `me rebuild(content: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has rebuild to reparse content")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("me rebuild(content: text)")).to_equal(true)
```

</details>

### editor block model — block kinds

#### parses heading blocks from # lines

- parses heading blocks from # lines
   - Expected: src contains `kind: "heading"`
   - Expected: src contains `_adapt_heading`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses heading blocks from # lines")
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"heading\"")).to_equal(true)
expect(src.contains("_adapt_heading")).to_equal(true)
```

</details>

#### parses code blocks between triple backticks

- parses code blocks between triple backticks
   - Expected: src contains `kind: "code"`
   - Expected: src contains `_adapt_code_block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses code blocks between triple backticks")
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"code\"")).to_equal(true)
expect(src.contains("_adapt_code_block")).to_equal(true)
```

</details>

#### parses list blocks from - or * or numbered

- parses list blocks from - or * or numbered
   - Expected: src contains `kind: "list"`
   - Expected: src contains `_adapt_list`
   - Expected: src contains `unordered_list`
   - Expected: src contains `ordered_list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses list blocks from - or * or numbered")
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"list\"")).to_equal(true)
expect(src.contains("_adapt_list")).to_equal(true)
expect(src.contains("unordered_list")).to_equal(true)
expect(src.contains("ordered_list")).to_equal(true)
```

</details>

#### parses table blocks from | lines

- parses table blocks from | lines
   - Expected: src contains `kind: "table"`
   - Expected: src contains `_adapt_table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses table blocks from | lines")
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"table\"")).to_equal(true)
expect(src.contains("_adapt_table")).to_equal(true)
```

</details>

#### parses paragraph blocks as default

- parses paragraph blocks as default
   - Expected: src contains `kind: "paragraph"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses paragraph blocks as default")
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"paragraph\"")).to_equal(true)
```

</details>

### editor markdown renderer — output

#### defines md_render_block function

- defines md_render_block function
   - Expected: src contains `fn md_render_block(block: RenderBlock) -> [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines md_render_block function")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_block(block: RenderBlock) -> [text]")).to_equal(true)
```

</details>

#### defines md_render_blocks for full model

- defines md_render_blocks for full model
   - Expected: src contains `fn md_render_blocks(model: BlockModel) -> [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines md_render_blocks for full model")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_blocks(model: BlockModel) -> [text]")).to_equal(true)
```

</details>

#### shows raw source for active blocks

- shows raw source for active blocks
   - Expected: src contains `model.is_active(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows raw source for active blocks")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("model.is_active(i)")).to_equal(true)
```

</details>

#### renders headings with bold ANSI styling

- renders headings with bold ANSI styling
   - Expected: src contains `_mdr_sgr("heading_1", "33")`
   - Expected: src contains `_mdr_sgr("heading_2", "36")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders headings with bold ANSI styling")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("_mdr_sgr(\"heading_1\", \"33\")")).to_equal(true)
expect(src.contains("_mdr_sgr(\"heading_2\", \"36\")")).to_equal(true)
```

</details>

#### renders code blocks with dim border

- renders code blocks with dim border
   - Expected: src contains `\\x1b[90m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders code blocks with dim border")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("\\x1b[90m")).to_equal(true)
```

</details>

#### renders inline bold, italic, and code

- renders inline bold, italic, and code
   - Expected: src contains `fn md_render_inline(line: text) -> text`
   - Expected: src contains `\\x1b[1m`
   - Expected: src contains `\\x1b[3m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders inline bold, italic, and code")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_inline(line: text) -> text")).to_equal(true)
expect(src.contains("\\x1b[1m")).to_equal(true)
expect(src.contains("\\x1b[3m")).to_equal(true)
```

</details>

#### renders inactive markdown blocks while preserving active-block source

- renders inactive markdown blocks while preserving active-block source
   - Expected: rendered[0] contains `Title`
   - Expected: rendered[0] does not contain `#`
   - Expected: active[0] equals `# Title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders inactive markdown blocks while preserving active-block source")
var model = BlockModel(
    blocks: [
        RenderBlock(id: 1, kind: "heading", from_line: 0, to_line: 0, content: "# Title", rendered_lines: ["# Title"], status: "ok"),
        RenderBlock(id: 2, kind: "paragraph", from_line: 2, to_line: 2, content: "This is **bold** and `code`.", rendered_lines: ["This is **bold** and `code`."], status: "ok"),
        RenderBlock(id: 3, kind: "list", from_line: 4, to_line: 4, content: "- [ ] Task", rendered_lines: ["- [ ] Task"], status: "ok"),
        RenderBlock(id: 4, kind: "table", from_line: 6, to_line: 8, content: "| A | B |\n|---|---|\n| 1 | 2 |", rendered_lines: ["| A | B |", "|---|---|", "| 1 | 2 |"], status: "ok")
    ],
    active_block: -1,
    next_id: 5
)
val rendered = md_render_blocks(model)
expect(rendered.len()).to_be_greater_than(4)
expect(rendered[0].contains("Title")).to_equal(true)
expect(rendered[0].contains("#")).to_equal(false)

model.activate_block(0)
val active = md_render_blocks(model)
expect(active[0]).to_equal("# Title")
```

</details>

#### renders live preview with active source cursor and selection fidelity

- renders live preview with active source cursor and selection fidelity
   - Expected: pane.model.active_block equals `1`
   - Expected: preview_pane_source_line_to_render_line(pane, 2) equals `1`
   - Expected: pane.viewport_start equals `1`
   - Expected: rendered[0] contains `This is `
   - Expected: rendered[0] contains `**bold**`
   - Expected: rendered[0] contains `\x1b[7m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders live preview with active source cursor and selection fidelity")
val content = "# Title\n\nThis is **bold** text\n\n- item"
var pane = preview_pane_create(1)
pane = preview_pane_update_for_cursor(pane, content, 2)
var buffer = EditorBuffer.from_text(EditorBufferId(value: 1), content)
buffer.move_cursor(2, 8)
buffer.set_selection_range(2, 8, 2, 16)

val rendered = preview_pane_render_for_editor(pane, buffer, 5)

expect(pane.model.active_block).to_equal(1)
expect(preview_pane_source_line_to_render_line(pane, 2)).to_equal(1)
expect(pane.viewport_start).to_equal(1)
expect(rendered[0].contains("This is ")).to_equal(true)
expect(rendered[0].contains("**bold**")).to_equal(true)
expect(rendered[0].contains("\x1b[7m")).to_equal(true)
```

</details>

#### edits markdown table rows and columns

- edits markdown table rows and columns
   - Expected: row_edit.changed is true
   - Expected: row_edit.content contains `|  |  |`
   - Expected: row_edit.message equals `table row inserted`
   - Expected: col_edit.changed is true
   - Expected: col_edit.content contains `| A |  | B |`
   - Expected: col_edit.content contains `| --- | --- | --- |`
   - Expected: col_edit.message equals `table column inserted`
   - Expected: cell_edit.changed is true
   - Expected: cell_edit.content contains `| 1 | updated |`
   - Expected: cell_edit.message equals `table cell updated`
   - Expected: next_cell.found is true
   - Expected: next_cell.line equals `0`
   - Expected: next_cell.col equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edits markdown table rows and columns")
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"
val row_edit = md_table_insert_row_after(content, 2)
expect(row_edit.changed).to_equal(true)
expect(row_edit.content.contains("|  |  |")).to_equal(true)
expect(row_edit.message).to_equal("table row inserted")

val col_edit = md_table_insert_column_after(content, 0, 3)
expect(col_edit.changed).to_equal(true)
expect(col_edit.content.contains("| A |  | B |")).to_equal(true)
expect(col_edit.content.contains("| --- | --- | --- |")).to_equal(true)
expect(col_edit.message).to_equal("table column inserted")

val cell_edit = md_table_set_cell(content, 2, 1, "updated")
expect(cell_edit.changed).to_equal(true)
expect(cell_edit.content.contains("| 1 | updated |")).to_equal(true)
expect(cell_edit.message).to_equal("table cell updated")

val next_cell = md_table_next_cell(content, 0, 3)
expect(next_cell.found).to_equal(true)
expect(next_cell.line).to_equal(0)
expect(next_cell.col).to_equal(6)
```

</details>

#### navigates markdown table cells to the next row

- navigates markdown table cells to the next row
   - Expected: next_row.found is true
   - Expected: next_row.line equals `2`
   - Expected: next_row.col equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("navigates markdown table cells to the next row")
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val next_row = md_table_next_cell(content, 0, 6)
expect(next_row.found).to_equal(true)
expect(next_row.line).to_equal(2)
expect(next_row.col).to_equal(2)
```

</details>

#### navigates markdown table cells to the previous row

- navigates markdown table cells to the previous row
   - Expected: prev_cell.found is true
   - Expected: prev_cell.line equals `0`
   - Expected: prev_cell.col equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("navigates markdown table cells to the previous row")
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val prev_cell = md_table_prev_cell(content, 2, 2)
expect(prev_cell.found).to_equal(true)
expect(prev_cell.line).to_equal(0)
expect(prev_cell.col).to_equal(6)
```

</details>

#### navigates markdown table cells to the previous same-row cell

- navigates markdown table cells to the previous same-row cell
   - Expected: prev_same_row.found is true
   - Expected: prev_same_row.line equals `2`
   - Expected: prev_same_row.col equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("navigates markdown table cells to the previous same-row cell")
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val prev_same_row = md_table_prev_cell(content, 2, 6)
expect(prev_same_row.found).to_equal(true)
expect(prev_same_row.line).to_equal(2)
expect(prev_same_row.col).to_equal(2)
```

</details>

#### sets all markdown task states for batch operations

- sets all markdown task states for batch operations
   - Expected: done contains `- [x] One`
   - Expected: done contains `- [x] Two`
   - Expected: done contains `* [x] Three`
   - Expected: open contains `- [ ] One`
   - Expected: open contains `- [ ] Two`
   - Expected: open contains `* [ ] Three`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets all markdown task states for batch operations")
val content = "- [ ] One\n- [x] Two\nText\n* [ ] Three"
val done = md_tasks_set_checked(content, true)
expect(done.contains("- [x] One")).to_equal(true)
expect(done.contains("- [x] Two")).to_equal(true)
expect(done.contains("* [x] Three")).to_equal(true)
val open = md_tasks_set_checked(done, false)
expect(open.contains("- [ ] One")).to_equal(true)
expect(open.contains("- [ ] Two")).to_equal(true)
expect(open.contains("* [ ] Three")).to_equal(true)
```

</details>

#### renders inline emphasis and code spans without changing source text

- renders inline emphasis and code spans without changing source text
   - Expected: rendered contains `\x1b[1mbold\x1b[0m`
   - Expected: rendered contains `\x1b[3mem\x1b[0m`
   - Expected: rendered contains `\x1b[36mcode\x1b[0m`
   - Expected: source equals `This is **bold**, *em*, and `code`.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders inline emphasis and code spans without changing source text")
val source = "This is **bold**, *em*, and `code`."
val rendered = md_render_inline(source)
expect(rendered.contains("\x1b[1mbold\x1b[0m")).to_equal(true)
expect(rendered.contains("\x1b[3mem\x1b[0m")).to_equal(true)
expect(rendered.contains("\x1b[36mcode\x1b[0m")).to_equal(true)
expect(source).to_equal("This is **bold**, *em*, and `code`.")
```

</details>

#### adapts Obsidian callouts as rendered callout blocks

- adapts Obsidian callouts as rendered callout blocks
   - Expected: model.block_count() equals `1`
   - Expected: block.kind equals `callout`
   - Expected: rendered[0] contains `WARNING Watch`
   - Expected: rendered[0] does not contain `[!WARNING]`
   - Expected: rendered.len() equals `1`
   - Expected: open_rendered[1] contains `Keep`
   - Expected: open_rendered[1] contains `\x1b[1mfocus\x1b[0m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adapts Obsidian callouts as rendered callout blocks")
val model = BlockModel.from_markdown("> [!WARNING]- Watch\n> Keep **focus**")
expect(model.block_count()).to_equal(1)
val block = model.block_at(0)
expect(block.kind).to_equal("callout")
val rendered = md_render_block(block)
expect(rendered[0].contains("WARNING Watch")).to_equal(true)
expect(rendered[0].contains("[!WARNING]")).to_equal(false)
expect(rendered.len()).to_equal(1)
val open_model = BlockModel.from_markdown("> [!WARNING]+ Watch\n> Keep **focus**")
val open_rendered = md_render_block(open_model.block_at(0))
expect(open_rendered[1].contains("Keep")).to_equal(true)
expect(open_rendered[1].contains("\x1b[1mfocus\x1b[0m")).to_equal(true)
```

</details>

#### toggles Obsidian callout folded markers while preserving body

- toggles Obsidian callout folded markers while preserving body
   - Expected: folded.changed is true
   - Expected: folded.message equals `callout folded`
   - Expected: folded.content equals `> [!WARNING]- Watch\n> Keep focus`
   - Expected: unfolded.changed is true
   - Expected: unfolded.message equals `callout unfolded`
   - Expected: unfolded.content equals `> [!WARNING]+ Watch\n> Keep focus`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("toggles Obsidian callout folded markers while preserving body")
val content = "> [!WARNING] Watch\n> Keep focus"
val folded = md_callout_toggle_fold(content, 1)
expect(folded.changed).to_equal(true)
expect(folded.message).to_equal("callout folded")
expect(folded.content).to_equal("> [!WARNING]- Watch\n> Keep focus")
val unfolded = md_callout_toggle_fold(folded.content, 0)
expect(unfolded.changed).to_equal(true)
expect(unfolded.message).to_equal("callout unfolded")
expect(unfolded.content).to_equal("> [!WARNING]+ Watch\n> Keep focus")
```

</details>

#### adapts Obsidian embeds as rendered embed blocks

- adapts Obsidian embeds as rendered embed blocks
   - Expected: model.block_count() equals `1`
   - Expected: block.kind equals `embed`
   - Expected: rendered[0] contains `embed: Alpha embed -> Project Alpha`
   - Expected: rendered[0] does not contain `![[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adapts Obsidian embeds as rendered embed blocks")
val model = BlockModel.from_markdown("![[Project Alpha|Alpha embed]]")
expect(model.block_count()).to_equal(1)
val block = model.block_at(0)
expect(block.kind).to_equal("embed")
val rendered = md_render_block(block)
expect(rendered[0].contains("embed: Alpha embed -> Project Alpha")).to_equal(true)
expect(rendered[0].contains("![[")).to_equal(false)
```

</details>

#### adapts markdown image attachments as rendered embed blocks

- adapts markdown image attachments as rendered embed blocks
   - Expected: block.kind equals `embed`
   - Expected: rendered[0] contains `image: Diagram -> assets/diagram.png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adapts markdown image attachments as rendered embed blocks")
val model = BlockModel.from_markdown("![Diagram](assets/diagram.png)")
val block = model.block_at(0)
expect(block.kind).to_equal("embed")
val rendered = md_render_block(block)
expect(rendered[0].contains("image: Diagram -> assets/diagram.png")).to_equal(true)
```

</details>

#### renders resolved Obsidian note embeds as transcluded target content

- renders resolved Obsidian note embeds as transcluded target content
   - Expected: rendered[0] contains `transclude: Alpha embed`
   - Expected: rendered[1] contains `Project Alpha`
   - Expected: rendered[2] contains `Ship renderer`
   - Expected: rendered[1] does not contain `status: active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders resolved Obsidian note embeds as transcluded target content")
val index = md_wiki_index_documents([
    md_wiki_document("/vault/Project Alpha.md", "---\nstatus: active\n---\n# Project Alpha\n- [ ] Ship renderer")
])
val model = BlockModel.from_markdown("![[Project Alpha|Alpha embed]]")
val rendered = md_render_block_with_wiki(model.block_at(0), index)
expect(rendered[0].contains("transclude: Alpha embed")).to_equal(true)
expect(rendered[1].contains("Project Alpha")).to_equal(true)
expect(rendered[2].contains("Ship renderer")).to_equal(true)
expect(rendered[1].contains("status: active")).to_equal(false)
```

</details>

#### renders nested resolved Obsidian note embeds recursively

- renders nested resolved Obsidian note embeds recursively
   - Expected: rendered[0] contains `transclude: Alpha embed`
   - Expected: rendered[2] contains `transclude: Beta embed`
   - Expected: rendered[3] contains `Project Beta`
   - Expected: rendered[4] contains `Nested body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders nested resolved Obsidian note embeds recursively")
val index = md_wiki_index_documents([
    md_wiki_document("/vault/Project Alpha.md", "# Project Alpha\n![[Project Beta|Beta embed]]"),
    md_wiki_document("/vault/Project Beta.md", "# Project Beta\nNested body")
])
val model = BlockModel.from_markdown("![[Project Alpha|Alpha embed]]")
val rendered = md_render_block_with_wiki(model.block_at(0), index)
expect(rendered[0].contains("transclude: Alpha embed")).to_equal(true)
expect(rendered[2].contains("transclude: Beta embed")).to_equal(true)
expect(rendered[3].contains("Project Beta")).to_equal(true)
expect(rendered[4].contains("Nested body")).to_equal(true)
```

</details>

### editor syntax highlight — tokens

#### defines StyledSegment with text_content and style_code

- defines StyledSegment with text_content and style_code
   - Expected: src contains `struct StyledSegment:`
   - Expected: src contains `text_content: text`
   - Expected: src contains `style_code: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines StyledSegment with text_content and style_code")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("struct StyledSegment:")).to_equal(true)
expect(src.contains("text_content: text")).to_equal(true)
expect(src.contains("style_code: text")).to_equal(true)
```

</details>

#### defines HighlightedLine with segments

- defines HighlightedLine with segments
   - Expected: src contains `struct HighlightedLine:`
   - Expected: src contains `segments: [StyledSegment]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines HighlightedLine with segments")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("struct HighlightedLine:")).to_equal(true)
expect(src.contains("segments: [StyledSegment]")).to_equal(true)
```

</details>

#### has highlight_spl_line for Simple language

- has highlight_spl_line for Simple language
   - Expected: src contains `fn highlight_spl_line(line: text) -> HighlightedLine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has highlight_spl_line for Simple language")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_spl_line(line: text) -> HighlightedLine")).to_equal(true)
```

</details>

#### has highlight_render for ANSI output

- has highlight_render for ANSI output
   - Expected: src contains `fn highlight_render(hl: HighlightedLine) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has highlight_render for ANSI output")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_render(hl: HighlightedLine) -> text")).to_equal(true)
```

</details>

#### recognizes Simple keywords

- recognizes Simple keywords
   - Expected: src contains `fn _hl_is_keyword(word: text) -> bool`
   - Expected: src contains `"fn"`
   - Expected: src contains `"val"`
   - Expected: src contains `"var"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes Simple keywords")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn _hl_is_keyword(word: text) -> bool")).to_equal(true)
expect(src.contains("\"fn\"")).to_equal(true)
expect(src.contains("\"val\"")).to_equal(true)
expect(src.contains("\"var\"")).to_equal(true)
```

</details>

#### recognizes Simple types

- recognizes Simple types
   - Expected: src contains `fn _hl_is_type(word: text) -> bool`
   - Expected: src contains `"i64"`
   - Expected: src contains `"text"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes Simple types")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn _hl_is_type(word: text) -> bool")).to_equal(true)
expect(src.contains("\"i64\"")).to_equal(true)
expect(src.contains("\"text\"")).to_equal(true)
```

</details>

#### highlights comments, strings, and numbers

- highlights comments, strings, and numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("highlights comments, strings, and numbers")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src).to_contain("ch == \"#\"")
expect(src).to_contain("ch == \"\\\"\"")
expect(src).to_contain("_hl_is_digit")
```

</details>

### editor block model — cursor helpers

#### has bm_cursor_block_index function

- has bm_cursor_block_index function
   - Expected: src contains `fn bm_cursor_block_index(model: BlockModel, cursor_row: i64) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has bm_cursor_block_index function")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_cursor_block_index(model: BlockModel, cursor_row: i64) -> i64")).to_equal(true)
```

</details>

#### has bm_cursor_block_changed function

- has bm_cursor_block_changed function
   - Expected: src contains `fn bm_cursor_block_changed(model: BlockModel, cursor_row: i64) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has bm_cursor_block_changed function")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_cursor_block_changed(model: BlockModel, cursor_row: i64) -> bool")).to_equal(true)
```

</details>

#### has bm_active_block_range function

- has bm_active_block_range function
   - Expected: src contains `fn bm_active_block_range(model: BlockModel) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has bm_active_block_range function")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_active_block_range(model: BlockModel) -> i64")).to_equal(true)
```

</details>

#### bm_cursor_block_index delegates to block_for_line

- bm_cursor_block_index delegates to block_for_line
   - Expected: src contains `model.block_for_line(cursor_row)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bm_cursor_block_index delegates to block_for_line")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("model.block_for_line(cursor_row)")).to_equal(true)
```

</details>

#### bm_cursor_block_changed compares to active_block

- bm_cursor_block_changed compares to active_block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bm_cursor_block_changed compares to active_block")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src).to_contain("current != model.active_block")
```

</details>

#### bm_active_block_range returns from_line of active block

- bm_active_block_range returns from_line of active block
   - Expected: src contains `model.blocks[idx].from_line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bm_active_block_range returns from_line of active block")
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("model.blocks[idx].from_line")).to_equal(true)
```

</details>

### editor markdown renderer — viewport

#### has md_render_blocks_for_tui function

- has md_render_blocks_for_tui function
   - Expected: src contains `fn md_render_blocks_for_tui(model: BlockModel, viewport_start: i64, viewport_... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has md_render_blocks_for_tui function")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_blocks_for_tui(model: BlockModel, viewport_start: i64, viewport_height: i64) -> [text]")).to_equal(true)
```

</details>

#### md_render_blocks_for_tui enforces viewport bounds

- md_render_blocks_for_tui enforces viewport bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("md_render_blocks_for_tui enforces viewport bounds")
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src).to_contain("if viewport_height <= 0")
expect(src).to_contain("viewport_start < 0")
expect(src).to_contain("val end = viewport_start + viewport_height")
```

</details>

### editor syntax highlight — dispatcher

#### has highlight_line dispatcher function

- has highlight_line dispatcher function
   - Expected: src contains `fn highlight_line(line: text, language_id: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has highlight_line dispatcher function")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_line(line: text, language_id: text) -> text")).to_equal(true)
```

</details>

#### highlight_line dispatches simple to highlight_spl_line

- highlight_line dispatches simple to highlight_spl_line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("highlight_line dispatches simple to highlight_spl_line")
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src).to_contain("language_id == \"simple\"")
expect(src).to_contain("highlight_render(hl)")
```

</details>

### editor markdown wiring — controller

#### markdown editing owns preview and outline visibility state

- markdown editing owns preview and outline visibility state
   - Expected: src contains `struct MdEditorState:`
   - Expected: src contains `preview_visible: bool`
   - Expected: src contains `outline_visible: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing owns preview and outline visibility state")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("struct MdEditorState:")).to_equal(true)
expect(src.contains("preview_visible: bool")).to_equal(true)
expect(src.contains("outline_visible: bool")).to_equal(true)
```

</details>

#### markdown language extension exposes IDE command routing

- markdown language extension exposes IDE command routing
   - Expected: src contains `ExtensionCommand(id: "md.preview"`
   - Expected: src contains `ExtensionCommand(id: "markdown.toggle_bold"`
   - Expected: src contains `ExtensionCommand(id: "md.toggleItalic"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown language extension exposes IDE command routing")
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("ExtensionCommand(id: \"md.preview\"")).to_equal(true)
expect(src.contains("ExtensionCommand(id: \"markdown.toggle_bold\"")).to_equal(true)
expect(src.contains("ExtensionCommand(id: \"md.toggleItalic\"")).to_equal(true)
```

</details>

#### editor extension roots discover user and system extension roots

- editor extension roots discover user and system extension roots
   - Expected: src contains `fn editor_extension_roots_from_inputs(configured_path_list: text, home: text)... (full value in folded executable source)`
   - Expected: src contains `".simple/editor/extensions"`
   - Expected: src contains `"/usr/share/simple/editor/extensions"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("editor extension roots discover user and system extension roots")
val src = read_text("src/lib/editor/extensions/roots.spl")
expect(src.contains("fn editor_extension_roots_from_inputs(configured_path_list: text, home: text) -> [text]")).to_equal(true)
expect(src.contains("\".simple/editor/extensions\"")).to_equal(true)
expect(src.contains("\"/usr/share/simple/editor/extensions\"")).to_equal(true)
```

</details>

#### markdown editing calls md_assist_on_enter

- markdown editing calls md_assist_on_enter
   - Expected: src contains `md_assist_on_enter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing calls md_assist_on_enter")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("md_assist_on_enter")).to_equal(true)
```

</details>

#### markdown editing calls md_assist_on_tab

- markdown editing calls md_assist_on_tab
   - Expected: src contains `md_assist_on_tab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing calls md_assist_on_tab")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("md_assist_on_tab")).to_equal(true)
```

</details>

#### command palette has selectable filtered entries

- command palette has selectable filtered entries
   - Expected: src contains `struct PaletteState:`
   - Expected: src contains `fn palette_show(state: PaletteState) -> PaletteState`
   - Expected: src contains `fn palette_select_next(state: PaletteState) -> PaletteState`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("command palette has selectable filtered entries")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("struct PaletteState:")).to_equal(true)
expect(src.contains("fn palette_show(state: PaletteState) -> PaletteState")).to_equal(true)
expect(src.contains("fn palette_select_next(state: PaletteState) -> PaletteState")).to_equal(true)
```

</details>

#### markdown commands expose palette entries

- markdown commands expose palette entries
   - Expected: src contains `md_commands_palette_entries`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown commands expose palette entries")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("md_commands_palette_entries")).to_equal(true)
```

</details>

#### editor document toggles markdown preview

- editor document toggles markdown preview
   - Expected: src contains `me toggle_markdown_preview(content: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("editor document toggles markdown preview")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("me toggle_markdown_preview(content: text) -> bool")).to_equal(true)
```

</details>

#### editor document toggles markdown outline

- editor document toggles markdown outline
   - Expected: src contains `me toggle_markdown_outline(content: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("editor document toggles markdown outline")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("me toggle_markdown_outline(content: text) -> bool")).to_equal(true)
```

</details>

#### markdown editing handles vim motion prefixes

- markdown editing handles vim motion prefixes
   - Expected: src contains `md_dispatch_motion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing handles vim motion prefixes")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("md_dispatch_motion")).to_equal(true)
```

</details>

#### markdown editing handles gx for opening links

- markdown editing handles gx for opening links
   - Expected: src contains `md_vim_open_link_under_cursor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing handles gx for opening links")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("md_vim_open_link_under_cursor")).to_equal(true)
```

</details>

### editor markdown wiring — document

#### EditorDocument has md_state field

- EditorDocument has md_state field
   - Expected: src contains `md_state: MarkdownState?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("EditorDocument has md_state field")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("md_state: MarkdownState?")).to_equal(true)
```

</details>

#### EditorDocument has cached_md_stats field

- EditorDocument has cached_md_stats field
   - Expected: src contains `cached_md_stats: MdDocStats`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("EditorDocument has cached_md_stats field")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("cached_md_stats: MdDocStats")).to_equal(true)
```

</details>

#### EditorDocument initializes md_state for markdown files

- EditorDocument initializes md_state for markdown files
   - Expected: src contains `md_state: nil`
   - Expected: src contains `md_compute_stats(content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("EditorDocument initializes md_state for markdown files")
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("md_state: nil")).to_equal(true)
expect(src.contains("md_compute_stats(content)")).to_equal(true)
```

</details>

### editor markdown wiring — commands

#### markdown commands run diagnostics

- markdown commands run diagnostics
   - Expected: src contains `md_diagnose`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown commands run diagnostics")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("md_diagnose")).to_equal(true)
```

</details>

#### command palette supports filtered commands

- command palette supports filtered commands
   - Expected: src contains `fn palette_update_query(state: PaletteState, query: text) -> PaletteState`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("command palette supports filtered commands")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("fn palette_update_query(state: PaletteState, query: text) -> PaletteState")).to_equal(true)
```

</details>

#### markdown commands have preview command alias

- markdown commands have preview command alias
   - Expected: src contains `markdown.togglePreview`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown commands have preview command alias")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("markdown.togglePreview")).to_equal(true)
```

</details>

#### markdown commands have outline command alias

- markdown commands have outline command alias
   - Expected: src contains `markdown.toggleOutline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown commands have outline command alias")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("markdown.toggleOutline")).to_equal(true)
```

</details>

### editor markdown wiring — tui shell

#### IDE TUI sanity renders preview pane

- IDE TUI sanity renders preview pane
   - Expected: src contains `preview_pane_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IDE TUI sanity renders preview pane")
val src = read_text("src/app/ide/tui_sanity.spl")
expect(src.contains("preview_pane_render")).to_equal(true)
```

</details>

#### IDE TUI sanity renders outline pane

- IDE TUI sanity renders outline pane
   - Expected: src contains `outline_panel_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IDE TUI sanity renders outline pane")
val src = read_text("src/app/ide/tui_sanity.spl")
expect(src.contains("outline_panel_render")).to_equal(true)
```

</details>

#### command palette owns visible overlay state

- command palette owns visible overlay state
   - Expected: src contains `visible: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("command palette owns visible overlay state")
val src = read_text("src/lib/editor/services/command_palette.spl")
expect(src.contains("visible: bool")).to_equal(true)
```

</details>

#### markdown stats expose status bar text

- markdown stats expose status bar text
   - Expected: src contains `md_stats_to_status_bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown stats expose status bar text")
val src = read_text("src/lib/editor/services/md_doc_stats.spl")
expect(src.contains("md_stats_to_status_bar")).to_equal(true)
```

</details>

### editor markdown wiring — md_dispatch glue

#### markdown editing defines command results

- markdown editing defines command results
   - Expected: src contains `struct MdCommandResult:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing defines command results")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("struct MdCommandResult:")).to_equal(true)
```

</details>

#### markdown commands have md_buffer_content

- markdown commands have md_buffer_content
   - Expected: src contains `fn md_buffer_content(buffer: EditorBuffer) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown commands have md_buffer_content")
val src = read_text("src/lib/editor/extensions/builtin/md_commands.spl")
expect(src.contains("fn md_buffer_content(buffer: EditorBuffer) -> text")).to_equal(true)
```

</details>

#### markdown editing has md_dispatch_motion

- markdown editing has md_dispatch_motion
   - Expected: src contains `fn md_dispatch_motion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing has md_dispatch_motion")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("fn md_dispatch_motion")).to_equal(true)
```

</details>

#### markdown editing routes all vim motions

- markdown editing routes all vim motions
   - Expected: src contains `md_vim_next_heading`
   - Expected: src contains `md_vim_prev_heading`
   - Expected: src contains `md_vim_next_sibling_heading`
   - Expected: src contains `md_vim_next_link`
   - Expected: src contains `md_vim_next_code_block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown editing routes all vim motions")
val src = read_text("src/lib/editor/view/md_editing.spl")
expect(src.contains("md_vim_next_heading")).to_equal(true)
expect(src.contains("md_vim_prev_heading")).to_equal(true)
expect(src.contains("md_vim_next_sibling_heading")).to_equal(true)
expect(src.contains("md_vim_next_link")).to_equal(true)
expect(src.contains("md_vim_next_code_block")).to_equal(true)
```

</details>

#### preview pane supports wiki-aware preview updates

- preview pane supports wiki-aware preview updates
   - Expected: src contains `fn preview_pane_update_with_wiki`
   - Expected: src contains `preview_pane_update_with_wiki`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preview pane supports wiki-aware preview updates")
val src = read_text("src/lib/editor/view/preview_pane.spl")
expect(src.contains("fn preview_pane_update_with_wiki")).to_equal(true)
expect(src.contains("preview_pane_update_with_wiki")).to_equal(true)
```

</details>

#### preview pane refreshes markdown preview with the open-note wiki index

- preview pane refreshes markdown preview with the open-note wiki index
   - Expected: src contains `preview_pane_update_with_wiki_for_cursor`
   - Expected: src contains `_preview_pane_model_for_cursor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preview pane refreshes markdown preview with the open-note wiki index")
val src = read_text("src/lib/editor/view/preview_pane.spl")
expect(src.contains("preview_pane_update_with_wiki_for_cursor")).to_equal(true)
expect(src.contains("_preview_pane_model_for_cursor")).to_equal(true)
```

</details>

### editor markdown wiring — gui shell

#### GUI backend renders markdown callout preview HTML

- GUI backend renders markdown callout preview HTML
   - Expected: src contains `md-callout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GUI backend renders markdown callout preview HTML")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("md-callout")).to_equal(true)
```

</details>

#### GUI backend renders markdown embed previews

- GUI backend renders markdown embed previews
   - Expected: src contains `md-embed-image-preview`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GUI backend renders markdown embed previews")
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("md-embed-image-preview")).to_equal(true)
```

</details>

#### IDE markdown render probe uses preview pane render

- IDE markdown render probe uses preview pane render
   - Expected: src contains `preview_pane_render`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IDE markdown render probe uses preview pane render")
val src = read_text("src/app/ide/markdown_render.spl")
expect(src.contains("preview_pane_render")).to_equal(true)
```

</details>

#### markdown stats are available for GUI status bars

- markdown stats are available for GUI status bars
   - Expected: src contains `md_stats_to_status_bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("markdown stats are available for GUI status bars")
val src = read_text("src/lib/editor/services/md_doc_stats.spl")
expect(src.contains("md_stats_to_status_bar")).to_equal(true)
```

</details>

### editor markdown property diagnostics

#### validates required and allowed frontmatter properties

- validates required and allowed frontmatter properties
   - Expected: diags.len() equals `3`
   - Expected: diags[0].message equals `Duplicate frontmatter property: status`
   - Expected: diags[1].message equals `Invalid frontmatter value for status: review`
   - Expected: diags[2].message equals `Frontmatter property requires a value: owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates required and allowed frontmatter properties")
val content = "---\nstatus: review\nstatus: duplicate\nowner: \n---\n# Note\n"
val diags = md_check_frontmatter_property_schema(content, "note.md", [
    md_property_schema_rule("status", true, ["active", "draft"]),
    md_property_schema_rule("owner", true, [])
])
expect(diags.len()).to_equal(3)
expect(diags[0].message).to_equal("Duplicate frontmatter property: status")
expect(diags[1].message).to_equal("Invalid frontmatter value for status: review")
expect(diags[2].message).to_equal("Frontmatter property requires a value: owner")
```

</details>

#### reports missing required frontmatter properties

- reports missing required frontmatter properties
   - Expected: diags.len() equals `1`
   - Expected: diags[0].message equals `Missing required frontmatter property: status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports missing required frontmatter properties")
val diags = md_check_frontmatter_property_schema("# Note\n", "note.md", [
    md_property_schema_rule("status", true, ["active", "draft"])
])
expect(diags.len()).to_equal(1)
expect(diags[0].message).to_equal("Missing required frontmatter property: status")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_markdown_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor block model — structure, editor block model — activation, editor block model — block kinds, editor markdown renderer — output, editor syntax highlight — tokens, editor block model — cursor helpers, editor markdown renderer — viewport, editor syntax highlight — dispatcher, editor markdown wiring — controller, editor markdown wiring — document, editor markdown wiring — commands, editor markdown wiring — tui shell, editor markdown wiring — md_dispatch glue, editor markdown wiring — gui shell, editor markdown property diagnostics.
- editor block model — structure
- editor block model — activation
- editor block model — block kinds
- editor markdown renderer — output
- editor syntax highlight — tokens
- editor block model — cursor helpers
- editor markdown renderer — viewport
- editor syntax highlight — dispatcher
- editor markdown wiring — controller
- editor markdown wiring — document
- editor markdown wiring — commands
- editor markdown wiring — tui shell
- editor markdown wiring — md_dispatch glue
- editor markdown wiring — gui shell
- editor markdown property diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 83 |
| Active scenarios | 83 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43bfcdb39e44b99255aabf11a503a8ee31165736e8db410fe599fa15ef38b759`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43bfcdb39e44b99255aabf11a503a8ee31165736e8db410fe599fa15ef38b759`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43bfcdb39e44b99255aabf11a503a8ee31165736e8db410fe599fa15ef38b759`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/editor_markdown_spec.spl
mirror: doc/06_spec/03_system/gui/editor_markdown_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_markdown_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_markdown_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_markdown_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/editor_markdown_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RenderBlock with id, kind, from_line, to_line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_markdown_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines BlockModel class with blocks and active_block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_markdown_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has from_markdown static constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
