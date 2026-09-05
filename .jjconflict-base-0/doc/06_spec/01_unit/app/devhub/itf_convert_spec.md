# Itf Convert Specification

> Tests covering ITF storage conversion.

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

- converts headings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts headings")
val storage = "<h1>Title</h1>"
val md = storage_to_markdown(storage)
expect(md).to_contain("# Title")
```

</details>

#### converts h2

- converts h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts h2")
val storage = "<h2>Subtitle</h2>"
val md = storage_to_markdown(storage)
expect(md).to_contain("## Subtitle")
```

</details>

#### converts bold

- converts bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bold")
val storage = "<p>This is <strong>bold</strong> text</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("**bold**")
```

</details>

#### converts italic

- converts italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts italic")
val storage = "<p>This is <em>italic</em> text</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("*italic*")
```

</details>

#### converts code

- converts code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts code")
val storage = "<p>Use <code>hello()</code> here</p>"
val md = storage_to_markdown(storage)
expect(md).to_contain("`hello()`")
```

</details>

#### converts list items

- converts list items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts list items")
val storage = "<ul><li>First</li><li>Second</li></ul>"
val md = storage_to_markdown(storage)
expect(md).to_contain("- First")
expect(md).to_contain("- Second")
```

</details>

#### converts hr

- converts hr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hr")
val storage = "<hr />"
val md = storage_to_markdown(storage)
expect(md).to_contain("---")
```

</details>

#### markdown_to_storage

#### converts headings

- converts headings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts headings")
val md = "# Title"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<h1>Title</h1>")
```

</details>

#### converts h2

- converts h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts h2")
val md = "## Subtitle"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<h2>Subtitle</h2>")
```

</details>

#### converts bold

- converts bold


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bold")
val md = "This is **bold** text"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<strong>bold</strong>")
```

</details>

#### converts italic

- converts italic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts italic")
val md = "This is *italic* text"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<em>italic</em>")
```

</details>

#### converts list items

- converts list items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts list items")
val md = "- First\n- Second"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<li>")
expect(storage).to_contain("First")
```

</details>

#### converts hr

- converts hr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts hr")
val md = "---"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<hr />")
```

</details>

#### wraps paragraphs in p tags

- wraps paragraphs in p tags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps paragraphs in p tags")
val md = "Hello world"
val storage = markdown_to_storage(md)
expect(storage).to_contain("<p>")
```

</details>

#### round-trip

#### preserves confluence macros through round-trip

- preserves confluence macros through round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves confluence macros through round-trip")
val original = "<h1>Title</h1>\n<p>Text</p>"
val md = storage_to_markdown(original)
expect(md).to_contain("# Title")
expect(md).to_contain("Text")
```

</details>

#### preserves fenced raw blocks

- preserves fenced raw blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves fenced raw blocks")
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
| Source | `test/01_unit/app/devhub/itf_convert_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ITF storage conversion.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2cc4278350f0110346b20cb7a7d0f9ec75223bedfac2da781e11bf49e5be5ff6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2cc4278350f0110346b20cb7a7d0f9ec75223bedfac2da781e11bf49e5be5ff6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2cc4278350f0110346b20cb7a7d0f9ec75223bedfac2da781e11bf49e5be5ff6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/devhub/itf_convert_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/itf_convert_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/itf_convert_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/itf_convert_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/itf_convert_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts headings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/itf_convert_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts h2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/itf_convert_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts bold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
