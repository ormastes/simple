# Md Editing Specification

> <details>

<!-- sdn-diagram:id=md_editing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_editing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_editing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_editing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Editing Specification

## Scenarios

### markdown table editing

#### inserts rows, columns, updates cells, and navigates cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
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

val cell_edit = md_table_set_cell(content, 2, 1, "updated")
expect(cell_edit.changed).to_equal(true)
expect(cell_edit.content.contains("| 1 | updated |")).to_equal(true)

val next_cell = md_table_next_cell(content, 0, 6)
expect(next_cell.found).to_equal(true)
expect(next_cell.line).to_equal(2)
expect(next_cell.col).to_equal(2)

val prev_cell = md_table_prev_cell(content, 2, 2)
expect(prev_cell.found).to_equal(true)
expect(prev_cell.line).to_equal(0)
expect(prev_cell.col).to_equal(6)
```

</details>

### markdown callouts and assists

#### toggles callout folded markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "> [!WARNING] Watch\n> Keep focus"
val folded = md_callout_toggle_fold(content, 1)
expect(folded.changed).to_equal(true)
expect(folded.content).to_equal("> [!WARNING]- Watch\n> Keep focus")
expect(folded.message).to_equal("callout folded")

val unfolded = md_callout_toggle_fold(folded.content, 0)
expect(unfolded.changed).to_equal(true)
expect(unfolded.content).to_equal("> [!WARNING]+ Watch\n> Keep focus")
expect(unfolded.message).to_equal("callout unfolded")
```

</details>

#### continues lists and toggles task states

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_assist_on_enter("- [ ] Task", 10)).to_equal("- [ ] ")
expect(md_assist_on_enter("  3. Item", 9)).to_equal("  4. ")
expect(md_assist_toggle_task("- [ ] Task")).to_equal("- [x] Task")
expect(md_tasks_set_checked("- [ ] One\n* [x] Two", false)).to_equal("- [ ] One\n* [ ] Two")
```

</details>

### markdown commands and motions

#### dispatches preview, outline, insert, stats, and task commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val outline = md_commands_dispatch("markdown.toggleOutline", state, "# Root", 0, 0)
expect(outline.status_message).to_equal("Outline shown")
expect(md_editor_state_outline_visible(md_command_result_state(outline))).to_equal(true)

val table = md_commands_dispatch("markdown.insertTable", md_command_result_state(outline), "", 0, 0)
expect(table.insert_text.contains("| Header 1 | Header 2 | Header 3 |")).to_equal(true)

val task = md_commands_dispatch("markdown.toggleTask", state, "- [ ] Task", 0, 0)
expect(task.replace_line).to_equal("- [x] Task")

val stats = md_commands_dispatch("markdown.documentStats", state, "one two\nthree", 0, 0)
expect(stats.status_message).to_contain("Lines: 2")
expect(stats.status_message).to_contain("Words: ~3")
```

</details>

#### moves through headings, links, and code fences

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# A\nbody\n## B\n[text](note.md)\n```\ncode\n```"
expect(md_dispatch_motion("]", "]", content, 0, 0).line).to_equal(2)
expect(md_dispatch_motion("]", "l", content, 0, 0).line).to_equal(3)
expect(md_dispatch_motion("]", "c", content, 0, 0).line).to_equal(4)
expect(md_vim_open_link_under_cursor(content, 3, 2)).to_equal("note.md")
```

</details>

### md_editing link and embed assist bounds

#### open_link_under_cursor on empty content returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_vim_open_link_under_cursor("", 0, 0)).to_equal("")
```

</details>

#### open_link_under_cursor with cursor line past end returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "[[MyNote]]"
expect(md_vim_open_link_under_cursor(content, 99, 0)).to_equal("")
```

</details>

#### open_link_under_cursor with negative cursor line returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "[[MyNote]]"
expect(md_vim_open_link_under_cursor(content, -1, 0)).to_equal("")
```

</details>

#### open_link_under_cursor resolves wiki link when cursor inside brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "[[MyNote]]"
expect(md_vim_open_link_under_cursor(content, 0, 3)).to_equal("MyNote")
```

</details>

#### open_link_under_cursor on empty line returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "\n\n"
expect(md_vim_open_link_under_cursor(content, 1, 0)).to_equal("")
```

</details>

#### open_link_under_cursor at EOF line with no link returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# heading"
expect(md_vim_open_link_under_cursor(content, 0, 0)).to_equal("")
```

</details>

### md_editing table bounds

#### table insert row on empty content returns no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_table_insert_row_after("", 0)
expect(result.changed).to_equal(false)
```

</details>

#### table insert row with negative cursor line returns no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |"
val result = md_table_insert_row_after(content, -1)
expect(result.changed).to_equal(false)
```

</details>

#### table insert row past last line returns no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |"
val result = md_table_insert_row_after(content, 99)
expect(result.changed).to_equal(false)
```

</details>

#### table set cell out-of-range col returns no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"
val result = md_table_set_cell(content, 2, 99, "x")
expect(result.changed).to_equal(false)
```

</details>

#### table set cell with negative line returns no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"
val result = md_table_set_cell(content, -1, 0, "x")
expect(result.changed).to_equal(false)
```

</details>

#### table next_cell on non-table line returns not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "plain text"
val result = md_table_next_cell(content, 0, 0)
expect(result.found).to_equal(false)
```

</details>

### md_editing assist on empty and edge input

#### assist on_enter with empty line returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_assist_on_enter("", 0)).to_equal("")
```

</details>

#### assist toggle task on plain text returns unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "plain text"
expect(md_assist_toggle_task(line)).to_equal("plain text")
```

</details>

#### assist toggle task on open task marks done

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_assist_toggle_task("- [ ] Do it")).to_equal("- [x] Do it")
```

</details>

#### assist toggle task on done task marks open

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_assist_toggle_task("- [x] Done")).to_equal("- [ ] Done")
```

</details>

#### document stats on empty content reports zero words

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_commands_dispatch("markdown.documentStats", md_editor_state_new(), "", 0, 0)
expect(result.status_message.contains("Lines:")).to_equal(true)
```

</details>

#### toggle task command on empty content returns not a task

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_commands_dispatch("markdown.toggleTask", md_editor_state_new(), "", 0, 0)
expect(result.status_message).to_equal("not a task")
```

</details>

#### toggle task command with cursor past last line returns not a task

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_commands_dispatch("markdown.toggleTask", md_editor_state_new(), "- [ ] Task", 99, 0)
expect(result.status_message).to_equal("not a task")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/md_editing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown table editing
- markdown callouts and assists
- markdown commands and motions
- md_editing link and embed assist bounds
- md_editing table bounds
- md_editing assist on empty and edge input

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
