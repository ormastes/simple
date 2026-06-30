# Itf Convert Specification

> <details>

<!-- sdn-diagram:id=itf_convert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=itf_convert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

itf_convert_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=itf_convert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Itf Convert Specification

## Scenarios

### ITF storage conversion

#### storage_to_markdown

#### converts headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<h1>Title</h1>"
val md = storage_to_markdown(storage)
expect(md).to_contain("# Title")
```

</details>

#### converts h2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<h2>Subtitle</h2>"
val md = storage_to_markdown(storage)
expect(md).to_contain("## Subtitle")
```

</details>

#### converts bold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<p>This is <strong>bold</strong> text</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("**bold**")
```

</details>

#### converts italic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<p>This is <em>italic</em> text</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("*italic*")
```

</details>

#### converts code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<p>Use <code>hello()</code> here</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("`hello()`")
```

</details>

#### converts list items

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<ul><li>First</li><li>Second</li></ul>"
val md = storage_to_markdown(storage)
expect(md).to_contain("- First")
expect(md).to_contain("- Second")
```

</details>

#### converts hr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val storage = "<hr />"
val md = storage_to_markdown(storage)
expect(md).to_contain("---")
```

</details>

#### markdown_to_storage

#### converts headings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Title"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<h1>Title</h1>")
```

</details>

#### converts h2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "## Subtitle"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<h2>Subtitle</h2>")
```

</details>

#### converts bold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "This is **bold** text"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<strong>bold</strong>")
```

</details>

#### converts italic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "This is *italic* text"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<em>italic</em>")
```

</details>

#### converts list items

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "- First\n- Second"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<li>")
expect(storage).to_contain("First")
```

</details>

#### converts hr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "---"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<hr />")
```

</details>

#### wraps paragraphs in p tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "Hello world"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<p>")
```

</details>

#### round-trip

#### preserves confluence macros through round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "<h1>Title</h1>\n<p>Text</p>"
val md = storage_to_markdown(original)
expect(md).to_contain("# Title")
expect(md).to_contain("Text")
```

</details>

#### preserves fenced raw blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Title\n\n~~~confluence-raw\n<ac:structured-macro ac:name=\"toc\"></ac:structured-macro>\n~~~\n\nParagraph"
val storage = markdown_to_storage(md)
expect(storage).to_contain("ac:structured-macro")
expect(storage).to_contain("<h1>Title</h1>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/itf_convert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ITF storage conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
