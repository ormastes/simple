# String Builder Enhanced Specification

> 1. sb push all

<!-- sdn-diagram:id=string_builder_enhanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_builder_enhanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_builder_enhanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_builder_enhanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Builder Enhanced Specification

## Scenarios

### StringBuilder push_all

#### pushes multiple parts at once

1. sb push all
   - Expected: sb.to_text() equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push_all(["hello", " ", "world"])
expect(sb.to_text()).to_equal("hello world")
```

</details>

#### handles empty array

1. sb push
2. sb push all
   - Expected: sb.to_text() equals `start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push("start")
sb.push_all([])
expect(sb.to_text()).to_equal("start")
```

</details>

#### handles single element array

1. sb push all
   - Expected: sb.to_text() equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push_all(["only"])
expect(sb.to_text()).to_equal("only")
```

</details>

### StringBuilder push_sep

#### adds separator between parts

1. sb push sep
2. sb push sep
3. sb push sep
   - Expected: sb.to_text() equals `a, b, c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push_sep("a", ", ")
sb.push_sep("b", ", ")
sb.push_sep("c", ", ")
expect(sb.to_text()).to_equal("a, b, c")
```

</details>

#### does not add separator before first part

1. sb push sep
   - Expected: sb.to_text() equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push_sep("first", ", ")
expect(sb.to_text()).to_equal("first")
```

</details>

#### works with newline separator

1. sb push sep
2. sb push sep
   - Expected: sb.to_text() equals `line1\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push_sep("line1", "\n")
sb.push_sep("line2", "\n")
expect(sb.to_text()).to_equal("line1\nline2")
```

</details>

### StringBuilder to_text_sep

#### joins parts with separator

1. sb push
2. sb push
3. sb push
   - Expected: sb.to_text_sep(", ") equals `x, y, z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push("x")
sb.push("y")
sb.push("z")
expect(sb.to_text_sep(", ")).to_equal("x, y, z")
```

</details>

#### returns empty string for empty builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
expect(sb.to_text_sep(", ")).to_equal("")
```

</details>

#### returns single part without separator

1. sb push
   - Expected: sb.to_text_sep(", ") equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = string_builder()
sb.push("only")
expect(sb.to_text_sep(", ")).to_equal("only")
```

</details>

### StringBuilder from_parts

#### creates builder from parts list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = StringBuilder.from_parts(["a", "b", "c"])
expect(sb.to_text()).to_equal("abc")
```

</details>

#### creates builder from empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = StringBuilder.from_parts([])
expect(sb.to_text()).to_equal("")
expect(sb.is_empty()).to_equal(true)
```

</details>

#### allows further pushes after from_parts

1. sb push
   - Expected: sb.to_text() equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sb = StringBuilder.from_parts(["hello"])
sb.push(" world")
expect(sb.to_text()).to_equal("hello world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_builder_enhanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StringBuilder push_all
- StringBuilder push_sep
- StringBuilder to_text_sep
- StringBuilder from_parts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
