# Md Renderer Callout Extended Specification

> <details>

<!-- sdn-diagram:id=md_renderer_callout_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_renderer_callout_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_renderer_callout_extended_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_renderer_callout_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Renderer Callout Extended Specification

## Scenarios

### callout extended robustness

#### callout type is uppercased in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!note] My Title\n> body"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered[0].contains("NOTE")).to_equal(true)
```

</details>

#### mixed-case callout type uppercased

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!Warning] heads up\n> content"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered[0].contains("WARNING")).to_equal(true)
```

</details>

#### callout with fold minus marker after bracket shows heading only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!note]- Hidden body\n> body text"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(1)
```

</details>

#### callout with fold plus marker after bracket is unfolded

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!note]+ Expanded\n> body text"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 2).to_equal(true)
```

</details>

#### callout fold marker inside bracket stripped from type name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!tip-] fold inside bracket\n> body"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
# type should be TIP not TIP-
expect(rendered[0].contains("TIP-")).to_equal(false)
expect(rendered[0].contains("TIP")).to_equal(true)
```

</details>

#### empty callout type > [!] renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!] title\n> body"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("callout")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### custom unknown callout type renders uppercased

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!mycustom] Custom\n> info"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered[0].contains("MYCUSTOM")).to_equal(true)
```

</details>

#### nested blockquote inside callout body renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!NOTE]\n> > inner quote\n> normal line"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 2).to_equal(true)
```

</details>

#### callout with no closing bracket > [!note does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!note some text\n> body"
val model = BlockModel.from_markdown(src)
expect(model.block_count() >= 1).to_equal(true)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### callout title with multi-byte UTF-8 renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "> [!note] 日本語タイトル\n> body"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

### embed and wiki-link edge cases

#### embed with anchor ![[note#section]] renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[note#section]]")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(1)
expect(rendered[0].contains("embed")).to_equal(true)
```

</details>

#### embed with alias ![[target|label]] shows label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[target|my label]]")
val rendered = md_render_block(model.block_at(0))
expect(rendered[0].contains("my label")).to_equal(true)
```

</details>

#### embed with empty alias ![[a|]] renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[a|]]")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### embed with very long target does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_target = ""
var j = 0
while j < 200:
    long_target = long_target + "a"
    j = j + 1
val src = "![[" + long_target + "]]"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### embed with UTF-8 target renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[日本語ノート]]")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### empty embed ![[]] renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![[]]")
expect(model.block_count() >= 1).to_equal(true)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 0).to_equal(true)
```

</details>

#### image embed with alt and URL renders as image

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![my alt](path/to/img.png)")
val rendered = md_render_block(model.block_at(0))
expect(rendered[0].contains("image")).to_equal(true)
```

</details>

#### image embed with empty alt renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("![](img.png)")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

### table edge cases

#### separator-only table renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| --- | --- |"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("table")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### table with extra columns on data row renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| A | B |\n| --- | --- |\n| 1 | 2 | 3 | 4 | 5 |"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(3)
```

</details>

#### table with fewer columns on data row renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| A | B | C |\n| --- | --- | --- |\n| 1 |"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(3)
```

</details>

#### single-column table renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "| Col |\n| --- |\n| val |"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(3)
```

</details>

#### table with all empty cells renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "|  |  |\n| --- | --- |\n|  |  |"
val model = BlockModel.from_markdown(src)
val rendered = md_render_block(model.block_at(0))
expect(rendered.len()).to_equal(3)
```

</details>

### general edge inputs

#### document of only CR characters does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("\r\r\r")
expect(model.block_count() >= 0).to_equal(true)
```

</details>

#### lone CR treated as whitespace or empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = md_render_inline("\r")
expect(result.len() >= 0).to_equal(true)
```

</details>

#### very long line in paragraph renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_line = ""
var j = 0
while j < 500:
    long_line = long_line + "x"
    j = j + 1
val model = BlockModel.from_markdown(long_line)
val rendered = md_render_blocks(model)
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### deeply nested list items render without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "- l1\n    - l2\n        - l3\n            - l4\n                - l5"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("list")
```

</details>

#### mixed list markers in sequence each get own block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "- dash item\n* star item\n+ plus item"
val model = BlockModel.from_markdown(src)
expect(model.block_count() >= 1).to_equal(true)
```

</details>

#### malformed ordered list 1text. is not a list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("1text. not a list")
val b = model.block_at(0)
expect(b.kind).to_equal("paragraph")
```

</details>

#### ordered list with very large number renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("999999. item")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("list")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_renderer_callout_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- callout extended robustness
- embed and wiki-link edge cases
- table edge cases
- general edge inputs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
