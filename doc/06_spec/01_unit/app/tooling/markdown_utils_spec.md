# Markdown Utils Specification

> <details>

<!-- sdn-diagram:id=markdown_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Utils Specification

## Scenarios

### Markdown Utilities

### Headers

#### creates h1

- expect h1


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect h1("Title") == "# Title"
```

</details>

#### creates h2

- expect h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect h2("Section") == "## Section"
```

</details>

#### creates h3

- expect h3


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect h3("Subsection") == "### Subsection"
```

</details>

#### creates heading with level

- expect heading


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect heading("Test", 4) == "#### Test"
```

</details>

### Text Formatting

#### creates bold

- expect bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect bold("text") == "**text**"
```

</details>

#### creates italic

- expect italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect italic("text") == "*text*"
```

</details>

#### creates bold italic

- expect bold italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect bold_italic("text") == "***text***"
```

</details>

#### creates inline code

- expect code


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect code("variable") == "`variable`"
```

</details>

#### creates strikethrough

- expect strikethrough


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect strikethrough("old") == "~~old~~"
```

</details>

### Links

#### creates link

- expect result == "[Google]


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = link(txt="Google", url="https://google.com")
expect result == "[Google](https://google.com)"
```

</details>

#### creates image

- expect result == "![Alt text]


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = image(alt="Alt text", url="/path/to/image.png")
expect result == "![Alt text](/path/to/image.png)"
```

</details>

#### creates link with title

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = link_with_title(txt="Link", url="https://example.com", title_txt="Example")
expect result.contains("[Link]")
expect result.contains("Example")
```

</details>

#### creates reference link

- expect reference link


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect reference_link(txt="Text", ref="ref1") == "[Text][ref1]"
```

</details>

### Lists

#### creates unordered list

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = unordered_list(["Apple", "Banana", "Cherry"])
expect result.contains("- Apple")
expect result.contains("- Banana")
expect result.contains("- Cherry")
```

</details>

#### creates ordered list

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ordered_list(["First", "Second", "Third"])
expect result.contains("1. First")
expect result.contains("2. Second")
expect result.contains("3. Third")
```

</details>

#### creates checklist items

- expect checked contains
- expect unchecked contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checked = checklist_item("Done task", true)
expect checked.contains("[x]")

val unchecked = checklist_item("Todo task", false)
expect unchecked.contains("[ ]")
```

</details>

### Code Blocks

#### creates code block with language

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = code_block(code_text="fn main():\n    pass", lang="simple")
expect result.contains("```simple")
expect result.contains("fn main()")
expect result.contains("```")
```

</details>

#### creates plain code block

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = code_block_plain("some code")
expect result.contains("```")
expect result.contains("some code")
```

</details>

### Blockquotes

#### creates blockquote

- expect blockquote


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect blockquote("Quote") == "> Quote"
```

</details>

#### creates multi-line blockquote

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = blockquote_multi(["Line 1", "Line 2"])
expect result.contains("> Line 1")
expect result.contains("> Line 2")
```

</details>

### Horizontal Rules

#### creates horizontal rule

- expect horizontal rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect horizontal_rule() == "---"
```

</details>

#### creates hr alias

- expect hr


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect hr() == "---"
```

</details>

### Tables

#### creates table

- expect result contains
- expect result contains
- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["Name", "Age"]
val rows = [
    ["Alice", "30"],
    ["Bob", "25"]
]
val result = table(headers, rows)
expect result.contains("Name")
expect result.contains("Age")
expect result.contains("Alice")
expect result.contains("---")
expect result.contains("|")
```

</details>

#### creates table with alignment

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["Left", "Center", "Right"]
val rows = [["A", "B", "C"]]
val alignments = [TableAlign.Left, TableAlign.Center, TableAlign.Right]
val result = table_with_align(headers, rows, alignments)
expect result.contains(":---")
expect result.contains(":---:")
expect result.contains("---:")
```

</details>

### Task Lists

#### creates task list

-
-
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tasks = [
    ("Complete task", true),
    ("Pending task", false)
]
val result = task_list(tasks)
expect result.contains("[x] Complete task")
expect result.contains("[ ] Pending task")
```

</details>

### Definitions

#### creates definition

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = definition(term="Term", desc="Definition text")
expect result.contains("Term")
expect result.contains(": Definition text")
```

</details>

### Footnotes

#### creates footnote reference

- expect footnote ref


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect footnote_ref("1") == "[^1]"
```

</details>

#### creates footnote definition

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = footnote_def(id="1", content="Footnote text")
expect result.contains("[^1]:")
expect result.contains("Footnote text")
```

</details>

### Document Structure

#### creates front matter

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = front_matter("title: Test\nauthor: Me")
expect result.contains("---")
expect result.contains("title: Test")
```

</details>

#### creates TOC placeholder

- expect toc


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect toc() == "<!-- TOC -->"
```

</details>

### Helpers

#### escapes markdown characters

- expect escaped contains
- expect escaped contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_markdown("*test* #heading")
expect escaped.contains("\\*")
expect escaped.contains("\\#")
```

</details>

#### creates document from sections

- MarkdownSection
- MarkdownSection
- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sections = [
    MarkdownSection(heading: "Intro", level: 1, content: "Welcome"),
    MarkdownSection(heading: "Details", level: 2, content: "More info")
]
val result = document(sections)
expect result.contains("# Intro")
expect result.contains("## Details")
expect result.contains("Welcome")
```

</details>

### Common Patterns

#### creates README template

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = readme_template(
    name="My Project",
    description="A cool project",
    installation="npm install my-project",
    usage="import my_project"
)
expect result.contains("# My Project")
expect result.contains("## Installation")
expect result.contains("## Usage")
```

</details>

#### creates badge

- expect result contains
- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = badge(label="build", value="passing", color="green")
expect result.contains("build")
expect result.contains("passing")
expect result.contains("green")
```

</details>

#### creates note

- expect result contains
- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = note("Important information")
expect result.contains("NOTE")
expect result.contains("Important information")
```

</details>

#### creates warning

- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = warning("Be careful")
expect result.contains("WARNING")
```

</details>

#### creates important

- expect result contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = important("Critical")
expect result.contains("IMPORTANT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/markdown_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Markdown Utilities
- Headers
- Text Formatting
- Links
- Lists
- Code Blocks
- Blockquotes
- Horizontal Rules
- Tables
- Task Lists
- Definitions
- Footnotes
- Document Structure
- Helpers
- Common Patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
