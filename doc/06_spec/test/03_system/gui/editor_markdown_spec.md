# Editor Markdown Specification

> <details>

<!-- sdn-diagram:id=editor_markdown_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_markdown_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_markdown_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_markdown_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 84 | 84 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Markdown Specification

## Scenarios

### editor block model — structure

#### defines RenderBlock with id, kind, from_line, to_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("class BlockModel:")).to_equal(true)
expect(src.contains("blocks: [RenderBlock]")).to_equal(true)
expect(src.contains("active_block: i64")).to_equal(true)
```

</details>

#### has from_markdown static constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("static fn from_markdown(content: text) -> BlockModel")).to_equal(true)
```

</details>

#### has block_count, block_at, block_for_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn block_count() -> i64")).to_equal(true)
expect(src.contains("fn block_at(index: i64) -> RenderBlock")).to_equal(true)
expect(src.contains("fn block_for_line(line: i64) -> i64")).to_equal(true)
```

</details>

### editor block model — activation

#### has activate_block and deactivate_block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("me activate_block(index: i64)")).to_equal(true)
expect(src.contains("me deactivate_block()")).to_equal(true)
```

</details>

#### has is_active to check block state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn is_active(index: i64) -> bool")).to_equal(true)
```

</details>

#### has rebuild to reparse content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("me rebuild(content: text)")).to_equal(true)
```

</details>

### editor block model — block kinds

#### parses heading blocks from # lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"heading\"")).to_equal(true)
expect(src.contains("_adapt_heading")).to_equal(true)
```

</details>

#### parses code blocks between triple backticks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"code\"")).to_equal(true)
expect(src.contains("_adapt_code_block")).to_equal(true)
```

</details>

#### parses list blocks from - or * or numbered

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"list\"")).to_equal(true)
expect(src.contains("_adapt_list")).to_equal(true)
expect(src.contains("unordered_list")).to_equal(true)
expect(src.contains("ordered_list")).to_equal(true)
```

</details>

#### parses table blocks from | lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"table\"")).to_equal(true)
expect(src.contains("_adapt_table")).to_equal(true)
```

</details>

#### parses paragraph blocks as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/markdown/adapter.spl")
expect(src.contains("kind: \"paragraph\"")).to_equal(true)
```

</details>

### editor markdown renderer — output

#### defines md_render_block function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_block(block: RenderBlock) -> [text]")).to_equal(true)
```

</details>

#### defines md_render_blocks for full model

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_blocks(model: BlockModel) -> [text]")).to_equal(true)
```

</details>

#### shows raw source for active blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("model.is_active(i)")).to_equal(true)
```

</details>

#### renders headings with bold ANSI styling

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("\\x1b[1;33m")).to_equal(true)
expect(src.contains("\\x1b[1;36m")).to_equal(true)
```

</details>

#### renders code blocks with dim border

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("\\x1b[90m")).to_equal(true)
```

</details>

#### renders inline bold, italic, and code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_inline(line: text) -> text")).to_equal(true)
expect(src.contains("\\x1b[1m")).to_equal(true)
expect(src.contains("\\x1b[3m")).to_equal(true)
```

</details>

#### renders inactive markdown blocks while preserving active-block source

1. RenderBlock
2. RenderBlock
3. RenderBlock
4. RenderBlock
   - Expected: rendered[0] contains `Title`
   - Expected: rendered[0] does not contain `#`
5. model activate block
   - Expected: active[0] equals `# Title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var pane = preview pane create
2. pane = preview pane update for cursor
3. var buffer = EditorBuffer from text
4. buffer move cursor
5. buffer set selection range
   - Expected: pane.model.active_block equals `1`
   - Expected: preview_pane_source_line_to_render_line(pane, 2) equals `1`
   - Expected: pane.viewport_start equals `1`
   - Expected: rendered[0] contains `This is `
   - Expected: rendered[0] contains `**bold**`
   - Expected: rendered[0] contains `\x1b[7m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val next_row = md_table_next_cell(content, 0, 6)
expect(next_row.found).to_equal(true)
expect(next_row.line).to_equal(2)
expect(next_row.col).to_equal(2)
```

</details>

#### navigates markdown table cells to the previous row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val prev_cell = md_table_prev_cell(content, 2, 2)
expect(prev_cell.found).to_equal(true)
expect(prev_cell.line).to_equal(0)
expect(prev_cell.col).to_equal(6)
```

</details>

#### navigates markdown table cells to the previous same-row cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"

val prev_same_row = md_table_prev_cell(content, 2, 6)
expect(prev_same_row.found).to_equal(true)
expect(prev_same_row.line).to_equal(2)
expect(prev_same_row.col).to_equal(2)
```

</details>

#### sets all markdown task states for batch operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "This is **bold**, *em*, and `code`."
val rendered = md_render_inline(source)
expect(rendered.contains("\x1b[1mbold\x1b[0m")).to_equal(true)
expect(rendered.contains("\x1b[3mem\x1b[0m")).to_equal(true)
expect(rendered.contains("\x1b[36mcode\x1b[0m")).to_equal(true)
expect(source).to_equal("This is **bold**, *em*, and `code`.")
```

</details>

#### adapts Obsidian callouts as rendered callout blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![Diagram](assets/diagram.png)")
val block = model.block_at(0)
expect(block.kind).to_equal("embed")
val rendered = md_render_block(block)
expect(rendered[0].contains("image: Diagram -> assets/diagram.png")).to_equal(true)
```

</details>

#### renders resolved Obsidian note embeds as transcluded target content

1. md wiki document
   - Expected: rendered[0] contains `transclude: Alpha embed`
   - Expected: rendered[1] contains `Project Alpha`
   - Expected: rendered[2] contains `Ship renderer`
   - Expected: rendered[1] does not contain `status: active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. md wiki document
2. md wiki document
   - Expected: rendered[0] contains `transclude: Alpha embed`
   - Expected: rendered[2] contains `transclude: Beta embed`
   - Expected: rendered[3] contains `Project Beta`
   - Expected: rendered[4] contains `Nested body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("struct StyledSegment:")).to_equal(true)
expect(src.contains("text_content: text")).to_equal(true)
expect(src.contains("style_code: text")).to_equal(true)
```

</details>

#### defines HighlightedLine with segments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("struct HighlightedLine:")).to_equal(true)
expect(src.contains("segments: [StyledSegment]")).to_equal(true)
```

</details>

#### has highlight_spl_line for Simple language

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_spl_line(line: text) -> HighlightedLine")).to_equal(true)
```

</details>

#### has highlight_render for ANSI output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_render(hl: HighlightedLine) -> text")).to_equal(true)
```

</details>

#### recognizes Simple keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn _hl_is_keyword(word: text) -> bool")).to_equal(true)
expect(src.contains("\"fn\"")).to_equal(true)
expect(src.contains("\"val\"")).to_equal(true)
expect(src.contains("\"var\"")).to_equal(true)
```

</details>

#### recognizes Simple types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn _hl_is_type(word: text) -> bool")).to_equal(true)
expect(src.contains("\"i64\"")).to_equal(true)
expect(src.contains("\"text\"")).to_equal(true)
```

</details>

#### highlights comments, strings, and numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("ch == \"#\"")).to_equal(true)
expect(src.contains("ch == \"\\\"\"")).to_equal(true)
expect(src.contains("_hl_is_digit")).to_equal(true)
```

</details>

### editor block model — cursor helpers

#### has bm_cursor_block_index function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_cursor_block_index(model: BlockModel, cursor_row: i64) -> i64")).to_equal(true)
```

</details>

#### has bm_cursor_block_changed function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_cursor_block_changed(model: BlockModel, cursor_row: i64) -> bool")).to_equal(true)
```

</details>

#### has bm_active_block_range function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("fn bm_active_block_range(model: BlockModel) -> i64")).to_equal(true)
```

</details>

#### bm_cursor_block_index delegates to block_for_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("model.block_for_line(cursor_row)")).to_equal(true)
```

</details>

#### bm_cursor_block_changed compares to active_block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("current != model.active_block")).to_equal(true)
```

</details>

#### bm_active_block_range returns from_line of active block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/block_model.spl")
expect(src.contains("model.blocks[idx].from_line")).to_equal(true)
```

</details>

### editor markdown renderer — viewport

#### has md_render_blocks_for_tui function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("fn md_render_blocks_for_tui(model: BlockModel, viewport_start: i64, viewport_height: i64) -> [text]")).to_equal(true)
```

</details>

#### md_render_blocks_for_tui reuses md_render_blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/render/md_renderer.spl")
expect(src.contains("val all_lines = md_render_blocks(model)")).to_equal(true)
```

</details>

### editor syntax highlight — dispatcher

#### has highlight_line dispatcher function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("fn highlight_line(line: text, language_id: text) -> text")).to_equal(true)
```

</details>

#### highlight_line dispatches simple to highlight_spl_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/buffer/syntax_highlight.spl")
expect(src.contains("language_id == \"simple\"")).to_equal(true)
expect(src.contains("highlight_render(hl)")).to_equal(true)
```

</details>

### editor markdown wiring — controller

#### editor_controller has palette_state field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("palette_state: PaletteState")).to_equal(true)
```

</details>

#### editor_controller owns extension host for IDE command routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("extension_host: ExtensionHost")).to_equal(true)
expect(src.contains("extension_host_with_builtins()")).to_equal(true)
expect(src.contains("me _activate_active_language()")).to_equal(true)
expect(src.contains("me.extension_host.emit_event(\"onDidOpenTextDocument\", doc.path())")).to_equal(true)
```

</details>

#### editor_controller discovers workspace user and system extension roots

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl_src = read_text("src/app/editor/editor_controller.spl")
val app_roots_src = read_text("src/app/editor/editor_extension_roots.spl")
val lib_roots_src = read_text("src/lib/editor/extensions/roots.spl")
expect(ctrl_src.contains("host.discover_extensions(editor_extension_roots())")).to_equal(true)
expect(app_roots_src.contains("fn editor_extension_roots() -> [text]")).to_equal(true)
expect(app_roots_src.contains("\"SIMPLE_EDITOR_EXTENSION_PATH\"")).to_equal(true)
expect(app_roots_src.contains("rt_env_get(\"HOME\")")).to_equal(true)
expect(app_roots_src.contains("editor_extension_roots_from_inputs(configured, home)")).to_equal(true)
expect(lib_roots_src.contains("\".simple/editor/extensions\"")).to_equal(true)
expect(lib_roots_src.contains("\"/usr/share/simple/editor/extensions\"")).to_equal(true)
```

</details>

#### editor_controller calls md_assist_on_enter for markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("md_assist_on_enter")).to_equal(true)
```

</details>

#### editor_controller calls md_assist_on_tab for markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("md_assist_on_tab")).to_equal(true)
```

</details>

#### editor_controller has _dispatch_palette_key method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_palette_key(key: text)")).to_equal(true)
```

</details>

#### editor_controller has _open_palette method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _open_palette()")).to_equal(true)
```

</details>

#### editor_controller merges md_commands_palette_entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("md_commands_palette_entries")).to_equal(true)
```

</details>

#### editor_controller has _toggle_md_preview method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _toggle_md_preview()")).to_equal(true)
```

</details>

#### editor_controller has _toggle_md_outline method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _toggle_md_outline()")).to_equal(true)
```

</details>

#### editor_controller handles vim motion prefixes for markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("md_dispatch_motion")).to_equal(true)
```

</details>

#### editor_controller handles gx for opening links

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("md_vim_open_link_under_cursor")).to_equal(true)
```

</details>

### editor markdown wiring — document

#### EditorDocument has md_state field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("md_state: MarkdownState?")).to_equal(true)
```

</details>

#### EditorDocument has cached_md_stats field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("cached_md_stats: MdDocStats")).to_equal(true)
```

</details>

#### EditorDocument initializes md_state for markdown files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/document.spl")
expect(src.contains("MarkdownState.new()")).to_equal(true)
expect(src.contains("md_compute_stats(content)")).to_equal(true)
```

</details>

### editor markdown wiring — commands

#### commands.spl runs diagnostics on save for markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("md_diagnose")).to_equal(true)
```

</details>

#### commands.spl has palette command alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"palette\"")).to_equal(true)
```

</details>

#### commands.spl has preview command alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"preview\"")).to_equal(true)
```

</details>

#### commands.spl has outline command alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"outline\"")).to_equal(true)
```

</details>

### editor markdown wiring — tui shell

#### tui_shell renders preview pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("_tui_render_preview_pane")).to_equal(true)
```

</details>

#### tui_shell renders outline pane

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("_tui_render_outline_pane")).to_equal(true)
```

</details>

#### tui_shell renders palette overlay

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("_tui_render_palette")).to_equal(true)
```

</details>

#### tui_shell shows markdown stats in status bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("md_stats_to_status_bar")).to_equal(true)
```

</details>

### editor markdown wiring — md_dispatch glue

#### md_dispatch.spl exists with md_apply_result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/md_dispatch.spl")
expect(src.contains("fn md_apply_result(buffer: EditorBuffer, result: MdCommandResult)")).to_equal(true)
```

</details>

#### md_dispatch.spl has md_buffer_content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/md_dispatch.spl")
expect(src.contains("fn md_buffer_content(buffer: EditorBuffer) -> text")).to_equal(true)
```

</details>

#### md_dispatch.spl has md_dispatch_motion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/md_dispatch.spl")
expect(src.contains("fn md_dispatch_motion")).to_equal(true)
```

</details>

#### md_dispatch.spl routes all vim motions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/md_dispatch.spl")
expect(src.contains("md_vim_next_heading")).to_equal(true)
expect(src.contains("md_vim_prev_heading")).to_equal(true)
expect(src.contains("md_vim_next_sibling_heading")).to_equal(true)
expect(src.contains("md_vim_next_link")).to_equal(true)
expect(src.contains("md_vim_next_code_block")).to_equal(true)
```

</details>

#### md_dispatch.spl has md_update_preview

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/md_dispatch.spl")
expect(src.contains("fn md_update_preview")).to_equal(true)
expect(src.contains("fn md_update_preview_with_wiki")).to_equal(true)
expect(src.contains("preview_pane_update_with_wiki")).to_equal(true)
```

</details>

#### editor_controller refreshes markdown preview with the open-note wiki index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("me _update_markdown_preview")).to_equal(true)
expect(src.contains("md_update_preview_with_wiki(doc, buffer, index)")).to_equal(true)
```

</details>

### editor markdown wiring — gui shell

#### gui_shell wires Ctrl+P to _open_palette

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("_open_palette")).to_equal(true)
```

</details>

#### gui_shell wires Ctrl+Shift+V to _toggle_md_preview

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("_toggle_md_preview")).to_equal(true)
```

</details>

#### gui_shell renders preview pane HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("preview_pane_render")).to_equal(true)
```

</details>

#### gui_shell shows md stats in status bar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("md_stats_to_status_bar")).to_equal(true)
```

</details>

### editor markdown property diagnostics

#### validates required and allowed frontmatter properties

1. md property schema rule
2. md property schema rule
   - Expected: diags.len() equals `3`
   - Expected: diags[0].message equals `Duplicate frontmatter property: status`
   - Expected: diags[1].message equals `Invalid frontmatter value for status: review`
   - Expected: diags[2].message equals `Frontmatter property requires a value: owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. md property schema rule
   - Expected: diags.len() equals `1`
   - Expected: diags[0].message equals `Missing required frontmatter property: status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
| Total scenarios | 84 |
| Active scenarios | 84 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
