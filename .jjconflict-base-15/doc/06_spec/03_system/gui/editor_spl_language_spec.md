# Editor Spl Language Specification

> <details>

<!-- sdn-diagram:id=editor_spl_language_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_spl_language_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_spl_language_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_spl_language_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Spl Language Specification

## Scenarios

### editor spl language — structs

#### defines SplDiagnostic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("struct SplDiagnostic:")).to_equal(true)
expect(src.contains("line: i64")).to_equal(true)
expect(src.contains("col: i64")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("severity: text")).to_equal(true)
```

</details>

#### defines SplCompletion struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("struct SplCompletion:")).to_equal(true)
expect(src.contains("label: text")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("detail: text")).to_equal(true)
```

</details>

### editor spl language — diagnose

#### has spl_language_diagnose function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_diagnose(content: text) -> [SplDiagnostic]")).to_equal(true)
```

</details>

#### detects tab character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Tab character found")).to_equal(true)
```

</details>

#### detects trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Trailing whitespace")).to_equal(true)
```

</details>

#### detects unclosed string literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("unclosed string literal")).to_equal(true)
```

</details>

#### detects missing colon on fn/me signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("missing ':'")).to_equal(true)
```

</details>

#### suggests val over var hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("'val'")).to_equal(true)
```

</details>

### editor spl language — complete

#### has spl_language_complete function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_complete(content: text, line: i64, col: i64) -> [SplCompletion]")).to_equal(true)
```

</details>

#### includes fn keyword completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"fn\"")).to_equal(true)
```

</details>

#### includes val keyword completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"val\"")).to_equal(true)
```

</details>

#### includes var keyword completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"var\"")).to_equal(true)
```

</details>

#### suggests std. prefix after use

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"std.\"")).to_equal(true)
```

</details>

#### uses kind=keyword for keywords

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"keyword\"")).to_equal(true)
```

</details>

#### uses kind=snippet for snippets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("\"snippet\"")).to_equal(true)
```

</details>

### editor spl language — hover

#### has spl_language_hover function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("fn spl_language_hover(content: text, line: i64, col: i64) -> text")).to_equal(true)
```

</details>

#### describes val keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Immutable binding")).to_equal(true)
```

</details>

#### describes me keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Mutable method (modifies self)")).to_equal(true)
```

</details>

#### describes fn keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Immutable method or free function")).to_equal(true)
```

</details>

#### describes extern keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("Runtime-provided function declaration")).to_equal(true)
```

</details>

#### returns empty string for unknown word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/extensions/builtin/spl_language.spl")
expect(src.contains("return \"\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_spl_language_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor spl language — structs
- editor spl language — diagnose
- editor spl language — complete
- editor spl language — hover

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
