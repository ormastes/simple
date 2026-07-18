# Editor Markdown Document Decor Specification

> <details>

<!-- sdn-diagram:id=editor_markdown_document_decor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_markdown_document_decor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_markdown_document_decor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_markdown_document_decor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Markdown Document Decor Specification

## Scenarios

### markdown document decoration

#### parses page view, header, footer, and css file from frontmatter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decor = md_document_decor_parse("---\npage_view: true\nheader: Release Note\nfooter: Page 1\ncss_file: \"./modern.css\"\n---\n# Title")
expect(decor.page_view).to_equal(true)
expect(decor.header).to_equal("Release Note")
expect(decor.footer).to_equal("Page 1")
expect(decor.css_file).to_equal("./modern.css")
```

</details>

#### collects inline css fences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decor = md_document_decor_parse("# Title\n\n```css\n.md-page { color: red; }\n```\n\nBody")
expect(decor.inline_css).to_contain(".md-page")
expect(decor.inline_css).to_contain("color: red")
```

</details>

#### removes frontmatter and css fences from document body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = md_document_body_without_decor("---\npage_view: true\n---\n\n# Title\n\n```css\n.hidden {}\n```\n\nBody")
expect(body).to_equal("# Title\n\nBody")
```

</details>

#### adapts css fences as markdown css blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("```css\n.note { color: blue; }\n```")
expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("md_css")
```

</details>

#### renders css fences in TUI preview as a compact marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = RenderBlock(id: 1, kind: "md_css", from_line: 0, to_line: 2, content: "```css\n.x {}\n```", rendered_lines: ["```css", ".x {}", "```"], status: "ok")
val rendered = md_render_block(block)
expect(rendered.len()).to_equal(1)
expect(rendered[0].contains("[css]")).to_equal(true)
```

</details>

#### renders document page view with header, footer, external css, inline css, and body

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = gui_render_markdown_document("---\npage_view: true\nheader: Release Note\nfooter: Page 1\ncss_file: ./modern.css\n---\n\n# Title\n\n```css\n.md-page { color: red; }\n```\n\nBody")
expect(html).to_contain("class=\"md-document page-view\"")
expect(html).to_contain("data-page-view=\"true\"")
expect(html).to_contain("class=\"md-page-header\"")
expect(html).to_contain("Release Note")
expect(html).to_contain("class=\"md-page-footer\"")
expect(html).to_contain("Page 1")
expect(html).to_contain("href=\"./modern.css\"")
expect(html).to_contain("class=\"md-inline-css\"")
expect(html).to_contain("md-page")
expect(html).to_contain("<h1>Title</h1>")
expect(html).to_contain("<p>Body</p>")
expect(html.contains("page_view: true")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_markdown_document_decor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown document decoration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
