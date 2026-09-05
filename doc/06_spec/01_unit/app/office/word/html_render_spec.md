# Html Render Specification

> <details>

<!-- sdn-diagram:id=html_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_render_spec -> std
html_render_spec -> app
html_render_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Render Specification

## Scenarios

### word HTML render: block styling from the shared theme

#### renders a Heading1 as a bold 2em div.heading_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_block_html(_block(BlockKind.Heading1, "Title"))
expect(html).to_contain("class=\"heading_1\"")
expect(html).to_contain("font-size: 2em;")
expect(html).to_contain("font-weight: bold;")
expect(html).to_contain(">Title</div>")
```

</details>

#### renders a Paragraph with the resolver line-height

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_block_html(_block(BlockKind.Paragraph, "Body text"))
expect(html).to_contain("class=\"paragraph\"")
expect(html).to_contain("line-height: 1.5;")
expect(html).to_contain(">Body text</div>")
```

</details>

#### renders a Quote with an italic border-left style

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_block_html(_block(BlockKind.Quote, "Quoted"))
expect(html).to_contain("class=\"quote\"")
expect(html).to_contain("font-style: italic;")
expect(html).to_contain("border-left: 4px solid #cccccc;")
```

</details>

### word HTML render: whole document
_A document renders as a styled <article> wrapping each block._

#### wraps blocks in a document article

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = RichDocument(title: "Doc", blocks: [_block(BlockKind.Heading1, "H"), _block(BlockKind.Paragraph, "P")])
val html = render_document_html(doc)
expect(html).to_start_with("<article class=\"document\">")
expect(html).to_end_with("</article>")
expect(html).to_contain("class=\"heading_1\"")
expect(html).to_contain("class=\"paragraph\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word/html_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- word HTML render: block styling from the shared theme
- word HTML render: whole document

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
