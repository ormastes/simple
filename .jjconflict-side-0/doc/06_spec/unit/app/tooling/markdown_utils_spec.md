# Markdown Utils Specification

> Tests covering Markdown Utilities, Headers, Text Formatting, Links, Lists, Code Blocks, Blockquotes, Horizontal Rules, Tables, Task Lists, Definitions, Footnotes, Document Structure, Helpers, Common Patterns.

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

- creates h1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates h1")
expect h1("Title") == "# Title"
```

</details>

#### creates h2

- creates h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates h2")
expect h2("Section") == "## Section"
```

</details>

#### creates h3

- creates h3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates h3")
expect h3("Subsection") == "### Subsection"
```

</details>

#### creates heading with level

- creates heading with level


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates heading with level")
expect heading("Test", 4) == "#### Test"
```

</details>

### Text Formatting

#### creates bold

- creates bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates bold")
expect bold("text") == "**text**"
```

</details>

#### creates italic

- creates italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates italic")
expect italic("text") == "*text*"
```

</details>

#### creates bold italic

- creates bold italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates bold italic")
expect bold_italic("text") == "***text***"
```

</details>

#### creates inline code

- creates inline code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates inline code")
expect code("variable") == "`variable`"
```

</details>

#### creates strikethrough

- creates strikethrough


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates strikethrough")
expect strikethrough("old") == "~~old~~"
```

</details>

### Links

#### creates link

- creates link


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates link")
val result = link(txt="Google", url="https://google.com")
expect result == "[Google](https://google.com)"
```

</details>

#### creates image

- creates image


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates image")
val result = image(alt="Alt text", url="/path/to/image.png")
expect result == "![Alt text](/path/to/image.png)"
```

</details>

#### creates link with title

- creates link with title


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates link with title")
val result = link_with_title(txt="Link", url="https://example.com", title_txt="Example")
expect result.contains("[Link]")
expect result.contains("Example")
```

</details>

#### creates reference link

- creates reference link


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates reference link")
expect reference_link(txt="Text", ref="ref1") == "[Text][ref1]"
```

</details>

### Lists

#### creates unordered list

- creates unordered list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unordered list")
val result = unordered_list(["Apple", "Banana", "Cherry"])
expect result.contains("- Apple")
expect result.contains("- Banana")
expect result.contains("- Cherry")
```

</details>

#### creates ordered list

- creates ordered list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ordered list")
val result = ordered_list(["First", "Second", "Third"])
expect result.contains("1. First")
expect result.contains("2. Second")
expect result.contains("3. Third")
```

</details>

#### creates checklist items

- creates checklist items


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates checklist items")
val checked = checklist_item("Done task", true)
expect checked.contains("[x]")

val unchecked = checklist_item("Todo task", false)
expect unchecked.contains("[ ]")
```

</details>

### Code Blocks

#### creates code block with language

- creates code block with language


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates code block with language")
val result = code_block(code_text="fn main():\n    pass", lang="simple")
expect result.contains("```simple")
expect result.contains("fn main()")
expect result.contains("```")
```

</details>

#### creates plain code block

- creates plain code block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates plain code block")
val result = code_block_plain("some code")
expect result.contains("```")
expect result.contains("some code")
```

</details>

### Blockquotes

#### creates blockquote

- creates blockquote


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates blockquote")
expect blockquote("Quote") == "> Quote"
```

</details>

#### creates multi-line blockquote

- creates multi-line blockquote


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-line blockquote")
val result = blockquote_multi(["Line 1", "Line 2"])
expect result.contains("> Line 1")
expect result.contains("> Line 2")
```

</details>

### Horizontal Rules

#### creates horizontal rule

- creates horizontal rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates horizontal rule")
expect horizontal_rule() == "---"
```

</details>

#### creates hr alias

- creates hr alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates hr alias")
expect hr() == "---"
```

</details>

### Tables

#### creates table

- creates table


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates table")
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

- creates table with alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates table with alignment")
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

- creates task list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates task list")
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

- creates definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates definition")
val result = definition(term="Term", desc="Definition text")
expect result.contains("Term")
expect result.contains(": Definition text")
```

</details>

### Footnotes

#### creates footnote reference

- creates footnote reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates footnote reference")
expect footnote_ref("1") == "[^1]"
```

</details>

#### creates footnote definition

- creates footnote definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates footnote definition")
val result = footnote_def(id="1", content="Footnote text")
expect result.contains("[^1]:")
expect result.contains("Footnote text")
```

</details>

### Document Structure

#### creates front matter

- creates front matter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates front matter")
val result = front_matter("title: Test\nauthor: Me")
expect result.contains("---")
expect result.contains("title: Test")
```

</details>

#### creates TOC placeholder

- creates TOC placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates TOC placeholder")
expect toc() == "<!-- TOC -->"
```

</details>

### Helpers

#### escapes markdown characters

- escapes markdown characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes markdown characters")
val escaped = escape_markdown("*test* #heading")
expect escaped.contains("\\*")
expect escaped.contains("\\#")
```

</details>

#### creates document from sections

- creates document from sections


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates document from sections")
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

- creates README template


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates README template")
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

- creates badge


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates badge")
val result = badge(label="build", value="passing", color="green")
expect result.contains("build")
expect result.contains("passing")
expect result.contains("green")
```

</details>

#### creates note

- creates note


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates note")
val result = note("Important information")
expect result.contains("NOTE")
expect result.contains("Important information")
```

</details>

#### creates warning

- creates warning


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates warning")
val result = warning("Be careful")
expect result.contains("WARNING")
```

</details>

#### creates important

- creates important


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates important")
val result = important("Critical")
expect result.contains("IMPORTANT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/markdown_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Markdown Utilities, Headers, Text Formatting, Links, Lists, Code Blocks, Blockquotes, Horizontal Rules, Tables, Task Lists, Definitions, Footnotes, Document Structure, Helpers, Common Patterns.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de014523ff04c3ccf8692c56022e3d366eaa529ea6d63843ccfc428d3216b502`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de014523ff04c3ccf8692c56022e3d366eaa529ea6d63843ccfc428d3216b502`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de014523ff04c3ccf8692c56022e3d366eaa529ea6d63843ccfc428d3216b502`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/markdown_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/markdown_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/markdown_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/markdown_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/markdown_utils_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates h1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/markdown_utils_spec.spl:188:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates h2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/markdown_utils_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates h3' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
