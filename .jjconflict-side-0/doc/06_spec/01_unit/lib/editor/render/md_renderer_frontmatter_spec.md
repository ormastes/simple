# Md Renderer Frontmatter Specification

> <details>

<!-- sdn-diagram:id=md_renderer_frontmatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_renderer_frontmatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_renderer_frontmatter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_renderer_frontmatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Renderer Frontmatter Specification

## Scenarios

### frontmatter block parsing

#### well-formed frontmatter at line 0 produces frontmatter block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: Hello\nauthor: test\n---\n\n# Heading")
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("frontmatter")
expect(model.block_at(1).kind).to_equal("heading")
```

</details>

#### frontmatter block renders as empty lines (hidden)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: Hi\n---\n\n# Title")
val fm = model.block_at(0)
val rendered = md_render_block(fm)
expect(rendered.len()).to_equal(0)
```

</details>

#### unterminated frontmatter is not frontmatter (Obsidian rule: needs closing ---)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: no close\nkey: value")
expect(model.block_count() >= 1).to_equal(true)
expect(model.block_at(0).kind).to_equal("horizontal_rule")
```

</details>

#### empty frontmatter --- --- produces frontmatter block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\n---\n\nparagraph")
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("frontmatter")
```

</details>

#### --- not at line 0 is treated as horizontal rule not frontmatter

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title\n\n---\n\nparagraph")
var has_frontmatter = false
var has_hr = false
var idx = 0
while idx < model.block_count():
    val k = model.block_at(idx).kind
    if k == "frontmatter":
        has_frontmatter = true
    if k == "horizontal_rule":
        has_hr = true
    idx = idx + 1
expect(has_frontmatter).to_equal(false)
expect(has_hr).to_equal(true)
```

</details>

#### frontmatter with multi-byte utf8 values does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: 日本語タイトル\n---\n\n# Body")
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("frontmatter")
```

</details>

#### document of only frontmatter produces one block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: only\n---")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("frontmatter")
```

</details>

#### frontmatter followed immediately by content with no blank line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("---\ntitle: t\n---\n# Heading")
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("frontmatter")
expect(model.block_at(1).kind).to_equal("heading")
```

</details>

### tilde fence code block parsing

#### tilde fence is parsed as code block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("~~~python\nprint('hi')\n~~~")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### unterminated tilde fence at EOF does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("~~~\nhello world")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### tilde fence renders with info string as header

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("~~~ruby\nputs 'hi'\n~~~")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
expect(rendered[0].contains("ruby")).to_equal(true)
```

</details>

#### tilde fence without info string renders without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("~~~\nhello\n~~~")
val rendered = md_render_block(model.block_at(0))
expect(rendered.len() >= 1).to_equal(true)
```

</details>

#### tilde fence does not consume backtick code fence as its closer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "~~~\n```not-a-closer```\n~~~\nafter"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

#### backtick fence does not consume tilde fence as its closer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "```\n~~~not-a-closer~~~\n```\nafter"
val model = BlockModel.from_markdown(src)
expect(model.block_count()).to_equal(2)
expect(model.block_at(0).kind).to_equal("code")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_renderer_frontmatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- frontmatter block parsing
- tilde fence code block parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
