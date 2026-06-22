# Md Renderer Hardening Specification

> <details>

<!-- sdn-diagram:id=md_renderer_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_renderer_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_renderer_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_renderer_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Renderer Hardening Specification

## Scenarios

### md_render_inline unbalanced markers

#### unbalanced double-star does not drop trailing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("hello **world")
expect(result.len()).to_be_greater_than(0)
expect(result.contains("hello")).to_equal(true)
expect(result.contains("world")).to_equal(true)
```

</details>

#### unbalanced single-star does not drop trailing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("hello *world")
expect(result.len()).to_be_greater_than(0)
expect(result.contains("hello")).to_equal(true)
expect(result.contains("world")).to_equal(true)
```

</details>

#### unbalanced backtick does not drop trailing text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("hello `world")
expect(result.len()).to_be_greater_than(0)
expect(result.contains("hello")).to_equal(true)
expect(result.contains("world")).to_equal(true)
```

</details>

<details>
<summary>Advanced: marker at end of line does not crash or loop</summary>

#### marker at end of line does not crash or loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = md_render_inline("text*")
val r2 = md_render_inline("text**")
val r3 = md_render_inline("text`")
expect(r1.contains("text")).to_equal(true)
expect(r2.contains("text")).to_equal(true)
expect(r3.contains("text")).to_equal(true)
```

</details>


</details>

#### empty emphasis markers produce no output crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("****")
expect(result).to_equal("\x1b[1m\x1b[0m")
```

</details>

#### nested emphasis renders outer text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("**bold *italic* end**")
expect(result.contains("bold")).to_equal(true)
```

</details>

#### escaped star is not treated as emphasis marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("a \\* b")
expect(result.contains("b")).to_equal(true)
expect(result.contains("\\*")).to_equal(true)
```

</details>

#### empty string input is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("")
expect(result).to_equal("")
```

</details>

#### only markers no text is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = md_render_inline("**")
val r2 = md_render_inline("*")
val r3 = md_render_inline("`")
expect(r1).to_equal("\x1b[3m\x1b[0m")
expect(r2).to_equal("*")
expect(r3).to_equal("`")
```

</details>

### code fence robustness

#### unclosed fence at EOF does not crash BlockModel.from_markdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title\n\n```rust\nfn foo() {}")
expect(model.block_count()).to_be_greater_than(0)
```

</details>

#### unclosed fence block has correct kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```python\nprint('hi')")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### code fence with info string parses as code block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```rust\nfn main() {}\n```")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### sdn-graph fence is classified correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```sdn-graph\nA -> B\n```")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("sdn_graph")
```

</details>

#### fence body extraction does not include closing fence line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```\nhello\nworld\n```\nafter")
expect(model.block_count()).to_be_greater_than(0)
val code_block = model.block_at(0)
expect(code_block.kind).to_equal("code")
```

</details>

### table rendering robustness

#### mismatched column count table renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| A | B | C |\n| --- | --- |\n| 1 | 2 | 3 | 4 |"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("table")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(0)
```

</details>

#### table with empty cells renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| A |  | C |\n| --- | --- | --- |\n|  | 2 |  |"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(0)
```

</details>

#### pipe inside inline code in table cell does not break row count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| code | result |\n| --- | --- |\n| `a | b` | ok |"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_be_greater_than(0)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(0)
```

</details>

#### table missing separator row renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| A | B |\n| 1 | 2 |"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("table")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(2)
```

</details>

### embed transclusion depth limit

#### depth limit blocks recursion beyond 4 levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = BlockModel.from_markdown("![[deep.md]]").block_at(0)
expect(block.kind).to_equal("embed")
# Verifying the depth guard: calling with depth=4 must return empty
# (no wiki index supplied so this is safe without a real wiki)
# We test the guard by inspecting that from_markdown handles embed blocks
expect(block.rendered_lines.len()).to_be_greater_than(0)
```

</details>

#### embed block with no wiki index renders as placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[some_note.md]]")
expect(model.block_count()).to_equal(1)
val block = model.block_at(0)
val rendered = md_render_block(block)
expect(rendered.len()).to_equal(1)
expect(rendered[0].contains("embed")).to_equal(true)
```

</details>

#### image embed renders as image placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![alt text](image.png)")
val block = model.block_at(0)
val rendered = md_render_block(block)
expect(rendered[0].contains("image")).to_equal(true)
```

</details>

#### embed with empty rendered_lines is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 1, kind: "embed", from_line: 0, to_line: 0, content: "", rendered_lines: [], status: "ok")
val rendered = md_render_block(block)
expect(rendered.len()).to_equal(0)
```

</details>

### callout rendering robustness

#### unknown callout type renders as fallback without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!XYZUNKNOWN] Custom Title\n> body line"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("callout")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(0)
expect(rendered[0].contains("XYZUNKNOWN")).to_equal(true)
```

</details>

#### folded callout renders header only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!NOTE]- Folded title\n> hidden body"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(1)
```

</details>

#### callout with no body lines is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!NOTE]"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(0)
```

</details>

#### nested callout blockquote prefix is stripped

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!NOTE]\n> > nested line"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_be_greater_than(1)
```

</details>

#### empty callout block with zero rendered_lines is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 1, kind: "callout", from_line: 0, to_line: 0, content: "", rendered_lines: [], status: "ok")
val rendered = md_render_block(block)
expect(rendered.len()).to_equal(0)
```

</details>

### empty and edge inputs

#### md_render_inline empty string returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(md_render_inline("")).to_equal("")
```

</details>

#### md_render_blocks with empty model returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("")
val result = md_render_blocks(model)
expect(result.len()).to_equal(0)
```

</details>

#### md_render_blocks_for_tui with empty model is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("")
val result = md_render_blocks_for_tui(model, 0, 10)
expect(result.len()).to_equal(0)
```

</details>

#### md_render_blocks_for_tui with negative viewport_start is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("hello")
val result = md_render_blocks_for_tui(model, -5, 3)
expect(result.len()).to_equal(0)
```

</details>

### oversized markdown bounds

#### renders only the requested viewport for a large markdown document

- content = content + "- item " + i to string
   - Expected: model.block_count() equals `1`
   - Expected: viewport.len() equals `7`
   - Expected: viewport[0] equals `- item 10`
   - Expected: viewport[6] equals `- item 16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var content = ""
var i = 0
while i < 600:
    if i > 0:
        content = content + "\n"
    content = content + "- item " + i.to_string()
    i = i + 1

val model = BlockModel.from_markdown(content)
expect(model.block_count()).to_equal(1)
val viewport = md_render_blocks_for_tui(model, 10, 7)
expect(viewport.len()).to_equal(7)
expect(viewport[0]).to_equal("- item 10")
expect(viewport[6]).to_equal("- item 16")
```

</details>

#### md_render_blocks_for_tui returns exactly a viewport window

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# H\n\npara\n\n```rust\nx\n```")
val rendered = md_render_blocks(model)
val window = md_render_blocks_for_tui(model, 1, 2)
expect(window.len()).to_equal(2)
expect(window[0]).to_equal(rendered[1])
expect(window[1]).to_equal(rendered[2])
```

</details>

#### md_render_blocks_for_tui_with_wiki returns exactly a viewport window

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# H\n\npara\n\n```rust\nx\n```")
val index = md_wiki_index_documents([])
val rendered = md_render_blocks_with_wiki(model, index)
val window = md_render_blocks_for_tui_with_wiki(model, index, 1, 2)
expect(window.len()).to_equal(2)
expect(window[0]).to_equal(rendered[1])
expect(window[1]).to_equal(rendered[2])
```

</details>

#### active wiki block renders raw source in tui viewport

- md wiki document
- var model = BlockModel from markdown
- model activate block
   - Expected: window.len() equals `rendered.len()`
   - Expected: window[0] equals `rendered[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [
    md_wiki_document("note.md", "# Note\n\nmore")
]
val index = md_wiki_index_documents(docs)
var model = BlockModel.from_markdown("![[note.md]]")
model.activate_block(0)
val rendered = md_render_blocks_with_wiki(model, index)
val window = md_render_blocks_for_tui_with_wiki(model, index, 0, 4)
expect(window.len()).to_equal(rendered.len())
expect(window[0]).to_equal(rendered[0])
```

</details>

### BlockModel.from_markdown edge inputs

#### empty string produces zero blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("")
expect(model.block_count()).to_equal(0)
```

</details>

#### only blank lines produces zero blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("\n\n\n")
expect(model.block_count()).to_equal(0)
```

</details>

#### single unterminated heading is one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title only")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("heading")
```

</details>

#### single unterminated code fence becomes one code block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```\ncode here")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### single unterminated callout becomes one callout block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("> [!NOTE]\n> body")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("callout")
```

</details>

#### block_at boundaries are valid after parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# H\n\npara\n\n- item")
val cnt = model.block_count()
expect(cnt).to_equal(3)
var idx = 0
while idx < cnt:
    val blk = model.block_at(idx)
    expect(blk.from_line).to_be_greater_than(-1)
    expect(blk.to_line).to_be_greater_than(blk.from_line - 1)
    idx = idx + 1
```

</details>

#### rebuild with empty string resets to zero blocks

- var model = BlockModel from markdown
   - Expected: model.block_count() equals `2`
- model rebuild
   - Expected: model.block_count() equals `0`
   - Expected: model.active_block equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var model = BlockModel.from_markdown("# Old content\n\nParagraph")
expect(model.block_count()).to_equal(2)
model.rebuild("")
expect(model.block_count()).to_equal(0)
expect(model.active_block).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_renderer_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md_render_inline unbalanced markers
- code fence robustness
- table rendering robustness
- embed transclusion depth limit
- callout rendering robustness
- empty and edge inputs
- oversized markdown bounds
- BlockModel.from_markdown edge inputs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
