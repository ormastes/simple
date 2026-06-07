# Editor Md Language Specification

> <details>

<!-- sdn-diagram:id=editor_md_language_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_md_language_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_md_language_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_md_language_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Md Language Specification

## Scenarios

### md language — structs

#### defines MdDiagnostic with line, col, message, severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("struct MdDiagnostic:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("severity: text")).to_equal(true)
```

</details>

#### defines MdCompletion with label, kind, detail

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("struct MdCompletion:")).to_equal(true)
expect(src.contains("label: text")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("detail: text")).to_equal(true)
```

</details>

### md language — function signatures

#### defines md_language_diagnose returning [MdDiagnostic]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_diagnose(content: text) -> [MdDiagnostic]")).to_equal(true)
```

</details>

#### defines md_language_complete returning [MdCompletion]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_complete(content: text, line: i64, col: i64) -> [MdCompletion]")).to_equal(true)
```

</details>

#### defines md_language_hover returning text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("fn md_language_hover(content: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

### md language — diagnose logic

#### checks heading-space using char_at and '#'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("char_at")).to_equal(true)
expect(src.contains("\"#\"")).to_equal(true)
expect(src.contains("Heading requires a space after '#'")).to_equal(true)
```

</details>

#### detects empty links using contains ']()'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("\"[\"")).to_equal(true)
expect(src.contains("contains(\"]()\")")).to_equal(true)
expect(src.contains("Empty link target")).to_equal(true)
```

</details>

#### counts code fences using starts_with triple backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("starts_with(\"```\")")).to_equal(true)
expect(src.contains("fence_count")).to_equal(true)
expect(src.contains("fence_count % 2 != 0")).to_equal(true)
expect(src.contains("Unclosed code fence")).to_equal(true)
```

</details>

#### checks trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Trailing whitespace")).to_equal(true)
```

</details>

### md language — completion logic

#### suggests heading levels after #

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Heading level 2")).to_equal(true)
expect(src.contains("Heading level 3")).to_equal(true)
expect(src.contains("\"## \"")).to_equal(true)
expect(src.contains("\"### \"")).to_equal(true)
```

</details>

#### suggests link template after [

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("ends_with(\"[\")")).to_equal(true)
expect(src.contains("[text](url)")).to_equal(true)
```

</details>

#### suggests common languages after triple backtick

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("\"simple\"")).to_equal(true)
expect(src.contains("\"bash\"")).to_equal(true)
expect(src.contains("\"json\"")).to_equal(true)
expect(src.contains("\"python\"")).to_equal(true)
```

</details>

### md language — hover logic

#### returns heading level string for heading lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("Heading level ")).to_equal(true)
expect(src.contains("_md_heading_level")).to_equal(true)
```

</details>

#### returns language name for code fence lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("starts_with(\"```\")")).to_equal(true)
expect(src.contains("trimmed.slice(3")).to_equal(true)
```

</details>

#### returns URL when cursor is on a link

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/md_language.spl")
expect(src.contains("_md_find_link_url")).to_equal(true)
expect(src.contains("fn _md_find_link_url(line: text, col: i64) -> text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_md_language_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md language — structs
- md language — function signatures
- md language — diagnose logic
- md language — completion logic
- md language — hover logic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
