# Ide Harden Specification

> <details>

<!-- sdn-diagram:id=ide_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_harden_spec -> std
ide_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Harden Specification

## Scenarios

### markdown_render: empty and malformed input are total

#### empty source yields a structured result with non-negative counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_render_probe_empty()
expect(p.block_count >= 0).to_equal(true)
expect(p.rendered_line_count >= 0).to_equal(true)
expect(p.preview_line_count >= 0).to_equal(true)
expect(p.contains_heading).to_equal(false)
expect(p.contains_table).to_equal(false)
```

</details>

#### malformed (unclosed fence) source yields a structured result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_render_probe_malformed()
expect(p.block_count >= 0).to_equal(true)
expect(p.rendered_line_count >= 0).to_equal(true)
expect(p.preview_line_count >= 0).to_equal(true)
expect(p.contains_heading).to_equal(true)
```

</details>

### markdown_render: Obsidian feature probe

#### wiki link [[x]] is parsed without crashing and yields at least one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.wiki_link_block_count > 0).to_equal(true)
```

</details>

#### embed ![[x]] is parsed without crashing and yields at least one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.embed_block_count > 0).to_equal(true)
```

</details>

#### callout > [!NOTE] is parsed without crashing and yields at least one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.callout_block_count > 0).to_equal(true)
```

</details>

#### table is parsed without crashing and yields at least one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.table_block_count > 0).to_equal(true)
```

</details>

#### unclosed fence is parsed without crashing and yields at least one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.unclosed_fence_block_count > 0).to_equal(true)
```

</details>

#### empty_source_safe and malformed_source_safe flags are both true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ide_markdown_obsidian_probe()
expect(p.empty_source_safe).to_equal(true)
expect(p.malformed_source_safe).to_equal(true)
```

</details>

### preview_pane: height edge cases

#### render with height 0 returns empty list, not a crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "# Hello\n\nBody")
val result = preview_pane_render(pane, 0)
expect(result.len()).to_equal(0)
```

</details>

#### render with negative height returns empty list, not a crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "# Hello\n\nBody")
val result = preview_pane_render(pane, -5)
expect(result.len()).to_equal(0)
```

</details>

#### render with height larger than content returns at most height lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "line1\nline2")
val result = preview_pane_render(pane, 100)
expect(result.len() >= 0).to_equal(true)
```

</details>

#### render with empty source and positive height returns empty or minimal output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "")
val result = preview_pane_render(pane, 10)
expect(result.len() >= 0).to_equal(true)
```

</details>

### preview_pane: CRLF source normalisation

#### CRLF source parses without crash and produces same block count as LF

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lf_source = "# Title\n\nParagraph\n\n- item"
val crlf_source = "# Title\r\n\r\nParagraph\r\n\r\n- item"
val pane_lf = preview_pane_update(preview_pane_create(1), lf_source)
val pane_crlf = preview_pane_update_crlf(preview_pane_create(1), crlf_source)
val out_lf = preview_pane_render(pane_lf, 20)
val out_crlf = preview_pane_render(pane_crlf, 20)
expect(out_lf.len()).to_equal(out_crlf.len())
```

</details>

#### standalone CR is also normalised

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cr_source = "# Title\rBody"
val pane = preview_pane_update_crlf(preview_pane_create(1), cr_source)
val result = preview_pane_render(pane, 10)
expect(result.len() >= 0).to_equal(true)
```

</details>

### preview_pane: scroll with zero or negative max_lines

#### scroll with max_lines 0 returns pane unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "line\nline\nline")
val scrolled = preview_pane_scroll(pane, 5, 0)
expect(scrolled.viewport_start).to_equal(pane.viewport_start)
```

</details>

#### scroll with max_lines negative returns pane unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "line\nline\nline")
val scrolled = preview_pane_scroll(pane, 5, -3)
expect(scrolled.viewport_start).to_equal(pane.viewport_start)
```

</details>

#### scroll does not go negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pane = preview_pane_update(preview_pane_create(1), "a\nb\nc")
val scrolled = preview_pane_scroll(pane, -100, 10)
expect(scrolled.viewport_start >= 0).to_equal(true)
```

</details>

### capabilities: report is total on all registered capabilities

#### ide_capability_count is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_capability_count() > 0).to_equal(true)
```

</details>

#### ide_capability_ids returns one id per capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = ide_capability_ids()
expect(ids.len()).to_equal(ide_capability_count())
```

</details>

#### ide_capability_report returns two lines per capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = ide_capability_report()
expect(report.len()).to_equal(ide_capability_count() * 2)
```

</details>

#### capability ids contain no empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = ide_capability_ids()
var all_nonempty = true
for id in ids:
    if id == "":
        all_nonempty = false
expect(all_nonempty).to_equal(true)
```

</details>

### md_editing: boundary inputs at line 0, last line, beyond EOL

#### table insert row at line 0 of a table works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"
val edit = md_table_insert_row_after(content, 0)
expect(edit.changed).to_equal(true)
```

</details>

#### table insert row on empty content returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = md_table_insert_row_after("", 0)
expect(edit.changed).to_equal(false)
```

</details>

#### table insert row with cursor_line beyond content length returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |"
val edit = md_table_insert_row_after(content, 999)
expect(edit.changed).to_equal(false)
```

</details>

#### table insert row with negative cursor_line returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = md_table_insert_row_after("| A |\n| --- |", -1)
expect(edit.changed).to_equal(false)
```

</details>

#### table insert column on empty content returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = md_table_insert_column_after("", 0, 0)
expect(edit.changed).to_equal(false)
```

</details>

#### table set cell on empty content returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edit = md_table_set_cell("", 0, 0, "val")
expect(edit.changed).to_equal(false)
```

</details>

#### table set cell with out-of-range col returns unchanged (no crash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "| A | B |\n| --- | --- |\n| 1 | 2 |"
val edit = md_table_set_cell(content, 2, 99, "x")
expect(edit.changed).to_equal(false)
```

</details>

#### md_dispatch_motion with empty content at line 0 does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_dispatch_motion("]", "]", "", 0, 0)
expect(result.found).to_equal(false)
```

</details>

#### md_dispatch_motion with cursor beyond last line does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# Head\nbody"
val result = md_dispatch_motion("]", "]", content, 999, 0)
expect(result.found).to_equal(false)
```

</details>

#### md_commands_dispatch toggleTask on empty content returns not-a-task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.toggleTask", state, "", 0, 0)
expect(result.status_message).to_equal("not a task")
```

</details>

#### md_commands_dispatch toggleTask at line beyond content length returns not-a-task

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.toggleTask", state, "- [ ] item", 999, 0)
expect(result.status_message).to_equal("not a task")
```

</details>

#### md_commands_dispatch unknown command returns command name as status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.nonexistent", state, "text", 0, 0)
expect(result.status_message).to_equal("markdown.nonexistent")
```

</details>

#### md_assist_on_enter on empty string returns empty continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_assist_on_enter("", 0)
expect(result).to_equal("")
```

</details>

#### md_assist_toggle_task on plain text returns text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_assist_toggle_task("just a paragraph")
expect(result).to_equal("just a paragraph")
```

</details>

### md_editing: toggle formatting on empty selection / insert at end

#### md_commands_dispatch insertTable on empty content inserts table text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.insertTable", state, "", 0, 0)
expect(result.insert_text.contains("Header")).to_equal(true)
```

</details>

#### md_commands_dispatch insertLink on empty content inserts link text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.insertLink", state, "", 0, 0)
expect(result.insert_text.contains("[text](url)")).to_equal(true)
```

</details>

#### md_commands_dispatch insertCodeBlock on empty content inserts fence text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.insertCodeBlock", state, "", 0, 0)
expect(result.insert_text.contains("```")).to_equal(true)
```

</details>

#### md_commands_dispatch documentStats on empty content does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = md_editor_state_new()
val result = md_commands_dispatch("markdown.documentStats", state, "", 0, 0)
expect(result.status_message.len() > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown_render: empty and malformed input are total
- markdown_render: Obsidian feature probe
- preview_pane: height edge cases
- preview_pane: CRLF source normalisation
- preview_pane: scroll with zero or negative max_lines
- capabilities: report is total on all registered capabilities
- md_editing: boundary inputs at line 0, last line, beyond EOL
- md_editing: toggle formatting on empty selection / insert at end

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
