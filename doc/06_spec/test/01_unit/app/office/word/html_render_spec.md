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
| 18 | 18 | 0 | 0 |

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

#### escapes rich-text block content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_block_html(_block(BlockKind.Paragraph, "<b>raw</b>"))
expect(html).to_contain("&lt;b&gt;raw&lt;/b&gt;")
expect(html.contains("<b>raw</b>")).to_be(false)
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

### writer HTML render: markdown source

#### renders markdown as paper/document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("---\npage_view: true\nheader: Draft\n---\n\n# Title\n\nBody")
expect(html).to_start_with("<article class=\"md-paper-layout\"")
expect(html).to_contain("data-format=\"markdown-paper\"")
expect(html).to_contain("data-format-name=\"Writer Markdown\"")
expect(html).to_contain("data-line-count=\"3\"")
expect(html).to_contain("<header class=\"md-page-header\">Draft</header>")
expect(html).to_contain("<h1>Title</h1>")
expect(html).to_contain("<p>Body</p>")
```

</details>

#### escapes writer markdown content before HTML rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("# <script>alert(1)</script>")
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
```

</details>

#### sanitizes unsafe Writer Markdown stylesheet URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("---\ncss_file: javascript:alert(1)\n---\n\nBody")
expect(html).to_contain("<link rel=\"stylesheet\" href=\"#\">")
expect(html).to_contain("<p>Body</p>")
```

</details>

#### renders Writer Markdown tables and images as document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("| Name | Status |\n| --- | --- |\n| Alpha | Ready |\n\n![Diagram](diagram.png)")
expect(html).to_contain("<table class=\"md-writer-table\">")
expect(html).to_contain("<th>Name</th>")
expect(html).to_contain("<td>Ready</td>")
expect(html).to_contain("<figure class=\"md-writer-image\">")
expect(html).to_contain("<img src=\"diagram.png\" alt=\"Diagram\">")
```

</details>

#### sanitizes unsafe Writer Markdown image URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("![Bad <x>](javascript:alert(1))")
expect(html).to_contain("<img src=\"#\" alt=\"Bad &lt;x&gt;\">")
expect(html).to_contain("<figcaption>Bad &lt;x&gt;</figcaption>")
```

</details>

#### renders Writer Markdown inline links in paper HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("# [Docs](docs.md)\n\nSee [Guide <x>](guide.md?a=1&b=2)")
expect(html).to_contain("<h1><a href=\"docs.md\">Docs</a></h1>")
expect(html).to_contain("<p>See <a href=\"guide.md?a=1&amp;b=2\">Guide &lt;x&gt;</a></p>")
```

</details>

#### renders Writer Markdown bullet lists as document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("- First **item**\n* Second <safe>")
expect(html).to_contain("<ul class=\"md-writer-list\">")
expect(html).to_contain("<li>First <strong>item</strong></li>")
expect(html).to_contain("<li>Second &lt;safe&gt;</li>")
```

</details>

#### renders Writer Markdown task lists as document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("- [x] Done **safe**\n- [ ] Open <x>")
expect(html).to_contain("<ul class=\"md-writer-task-list\">")
expect(html).to_contain("data-task=\"true\" data-checked=\"true\"")
expect(html).to_contain("<input type=\"checkbox\" disabled checked>")
expect(html).to_contain("Done <strong>safe</strong>")
expect(html).to_contain("data-task=\"true\" data-checked=\"false\"")
expect(html).to_contain("<input type=\"checkbox\" disabled>")
expect(html).to_contain("Open &lt;x&gt;")
```

</details>

#### renders Writer Markdown ordered lists as document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("1. First **item**\n10. Second <safe>")
expect(html).to_contain("<ol class=\"md-writer-list md-writer-ordered-list\">")
expect(html).to_contain("<li>First <strong>item</strong></li>")
expect(html).to_contain("<li>Second &lt;safe&gt;</li>")
```

</details>

#### renders Writer Markdown blockquotes as document HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("> First **quote**\n> Second <safe>")
expect(html).to_contain("<blockquote class=\"md-writer-quote\">")
expect(html).to_contain("<p>First <strong>quote</strong></p>")
expect(html).to_contain("<p>Second &lt;safe&gt;</p>")
```

</details>

#### renders Writer Markdown thematic breaks as document rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("Before\n---\nAfter")
expect(html).to_contain("<p>Before</p><hr class=\"md-writer-rule\"><p>After</p>")
```

</details>

#### renders Writer Markdown fenced code as escaped code HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("```python\nprint(\"<x>\")\n```")
expect(html).to_contain("<pre class=\"md-writer-code\" data-language=\"python\"><code>print(&quot;&lt;x&gt;&quot;)</code></pre>")
```

</details>

#### preserves Markdown table alignment markers in Writer HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = render_writer_markdown_html("| Name | Score | Note |\n| :--- | ---: | :-: |\n| Alpha | 42 | ok |")
expect(html).to_contain("<th data-align=\"left\" style=\"text-align:left\">Name</th>")
expect(html).to_contain("<th data-align=\"right\" style=\"text-align:right\">Score</th>")
expect(html).to_contain("<td data-align=\"center\" style=\"text-align:center\">ok</td>")
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
- writer HTML render: markdown source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
