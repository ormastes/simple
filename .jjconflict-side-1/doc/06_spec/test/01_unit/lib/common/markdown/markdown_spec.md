# Markdown Specification

> <details>

<!-- sdn-diagram:id=markdown_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Specification

## Scenarios

### markdown_inline_text

#### returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("")).to_equal("")
```

</details>

#### passes plain text through unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("hello world")).to_equal("hello world")
```

</details>

#### wraps bold markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("**bold**")).to_equal("<strong>bold</strong>")
```

</details>

#### wraps italic markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("*italic*")).to_equal("<em>italic</em>")
```

</details>

#### wraps code span

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("`code`")).to_equal("<code>code</code>")
```

</details>

#### leaves unbalanced bold as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("**oops")).to_equal("**oops")
```

</details>

#### leaves unbalanced italic as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("*oops")).to_equal("*oops")
```

</details>

#### leaves unbalanced backtick as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("`oops")).to_equal("`oops")
```

</details>

#### handles escaped star

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("\\*literal\\*")).to_equal("*literal*")
```

</details>

#### protects code span content from bold parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("`**not bold**`")).to_equal("<code>**not bold**</code>")
```

</details>

#### handles adjacent bold and italic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_inline_text("**a** and *b*")).to_equal("<strong>a</strong> and <em>b</em>")
```

</details>

### markdown_escape_html

#### returns empty string for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("")).to_equal("")
```

</details>

#### escapes ampersand first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("&amp;")).to_equal("&amp;amp;")
```

</details>

#### escapes less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("<b>")).to_equal("&lt;b&gt;")
```

</details>

#### escapes greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html(">")).to_equal("&gt;")
```

</details>

#### escapes double-quote for attribute safety

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("say \"hi\"")).to_equal("say &quot;hi&quot;")
```

</details>

#### escapes single-quote for attribute safety

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("it's")).to_equal("it&#39;s")
```

</details>

#### escapes all together

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_escape_html("<a href=\"x&y\">")).to_equal("&lt;a href=&quot;x&amp;y&quot;&gt;")
```

</details>

### markdown_plain_inline

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("")).to_equal("")
```

</details>

#### strips bold markers, keeps text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("**bold**")).to_equal("bold")
```

</details>

#### strips italic markers, keeps text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("*italic*")).to_equal("italic")
```

</details>

#### strips backtick markers, keeps interior

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("`code`")).to_equal("code")
```

</details>

#### passes plain text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("hello")).to_equal("hello")
```

</details>

#### drops unbalanced bold markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("**oops")).to_equal("oops")
```

</details>

#### drops lone star in unbalanced italic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("*oops")).to_equal("oops")
```

</details>

#### keeps escaped star as literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("\\*literal\\*")).to_equal("*literal*")
```

</details>

#### code span protects ** from being stripped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_plain_inline("`**keep**`")).to_equal("**keep**")
```

</details>

### markdown_block_kind

#### identifies headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("# Hello")).to_equal("heading")
expect(markdown_block_kind("## Sub")).to_equal("heading")
```

</details>

#### identifies code fences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("```rust")).to_equal("code")
expect(markdown_block_kind("```")).to_equal("code")
```

</details>

#### identifies blockquotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("> quote")).to_equal("blockquote")
```

</details>

#### identifies lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("- item")).to_equal("list")
expect(markdown_block_kind("* item")).to_equal("list")
```

</details>

#### identifies tables by leading pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("| col1 | col2 |")).to_equal("table")
```

</details>

#### identifies separator rows as table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("| --- | --- |")).to_equal("table")
expect(markdown_block_kind("|:---:|---:|")).to_equal("table")
```

</details>

#### does NOT classify mid-paragraph pipe as table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("a | b")).to_equal("paragraph")
expect(markdown_block_kind("true | false logic")).to_equal("paragraph")
```

</details>

#### identifies plain paragraph

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("Just text")).to_equal("paragraph")
```

</details>

#### empty string is paragraph

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_block_kind("")).to_equal("paragraph")
```

</details>

### parse_markdown_blocks

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("")
expect(blocks.len()).to_equal(0)
```

</details>

#### skips blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("a\n\nb")
expect(blocks.len()).to_equal(2)
```

</details>

#### handles heading with no text (bare #)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("#")
expect(blocks.len()).to_equal(1)
expect(blocks[0].kind).to_equal("heading")
```

</details>

#### handles unclosed code fence at EOF without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("```\ncode line\nno close")
expect(blocks.len()).to_equal(3)
expect(blocks[0].kind).to_equal("code")
expect(blocks[1].kind).to_equal("code")
expect(blocks[2].kind).to_equal("code")
```

</details>

#### correctly closes a code fence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("```\nfoo\n```\nbar")
expect(blocks.len()).to_equal(4)
expect(blocks[3].kind).to_equal("paragraph")
```

</details>

#### preserves block from_line and to_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = parse_markdown_blocks("# H\n\npara")
expect(blocks[0].from_line).to_equal(0)
expect(blocks[1].from_line).to_equal(2)
```

</details>

### markdown_slugify

#### returns section for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("")).to_equal("section")
```

</details>

#### returns section for whitespace-only input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("   ")).to_equal("section")
```

</details>

#### lowercases and replaces spaces with dashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("Hello World")).to_equal("hello-world")
```

</details>

#### collapses repeated dashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("foo  bar")).to_equal("foo-bar")
```

</details>

#### strips leading and trailing dashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("  hello  ")).to_equal("hello")
```

</details>

#### strips punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("Hello, World!")).to_equal("hello-world")
```

</details>

#### handles unicode input without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slug = markdown_slugify("こんにちは")
expect(slug.len() > 0).to_equal(true)
```

</details>

#### handles already-slug input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_slugify("hello-world")).to_equal("hello-world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/markdown/markdown_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown_inline_text
- markdown_escape_html
- markdown_plain_inline
- markdown_block_kind
- parse_markdown_blocks
- markdown_slugify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
