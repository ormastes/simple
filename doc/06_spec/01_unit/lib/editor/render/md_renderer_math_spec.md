# Md Renderer Math Specification

> <details>

<!-- sdn-diagram:id=md_renderer_math_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_renderer_math_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_renderer_math_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_renderer_math_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Renderer Math Specification

## Scenarios

### math block parsing

#### multi-line $$ block parses as math kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$\nE = mc^2\n$$")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("math")
```

</details>

#### single-line $$...$$ parses as math kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$E = mc^2$$")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("math")
```

</details>

#### math block separates from surrounding paragraphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("before\n$$\nx\n$$\nafter")
expect(model.block_count()).to_equal(3)
expect(model.block_at(0).kind).to_equal("paragraph")
expect(model.block_at(1).kind).to_equal("math")
expect(model.block_at(2).kind).to_equal("paragraph")
```

</details>

#### unterminated $$ runs to end of document like unterminated code fence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$\nx = 1\ny = 2")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("math")
```

</details>

#### bare $$ alone is an unterminated math block, not a paragraph

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("math")
```

</details>

### math block rendering

#### renders dim math delimiters around styled body

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$\nE = mc^2\n$$")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(3)
expect(lines[0].index_of("math") >= 0).to_equal(true)
expect(lines[1].index_of("E = mc^2") >= 0).to_equal(true)
expect(lines[2].index_of("math") >= 0).to_equal(true)
```

</details>

#### single-line math renders as one line with body preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("$$a + b$$")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(1)
expect(lines[0].index_of("a + b") >= 0).to_equal(true)
```

</details>

#### multi-line body lines pass through verbatim

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No braces in the LaTeX sample: {x} in a string literal is parsed
# as interpolation by the Simple lexer.
val model = BlockModel.from_markdown("$$\n\\sum_i x_i\n\\alpha + \\beta\n$$")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(4)
expect(lines[1].index_of("\\sum_i x_i") >= 0).to_equal(true)
expect(lines[2].index_of("\\alpha + \\beta") >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_renderer_math_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- math block parsing
- math block rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
