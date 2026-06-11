# String Builder Specification

> 1. var sb = string builder

<!-- sdn-diagram:id=string_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Builder Specification

## Scenarios

### StringBuilder

### basic construction

#### creates empty builder

1. var sb = string builder
   - Expected: sb.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
expect(sb.is_empty()).to_equal(true)
```

</details>

#### creates builder from text

1. var sb = string builder from
   - Expected: sb.to_text() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder_from("hello")
expect(sb.to_text()).to_equal("hello")
```

</details>

### push and to_text

#### pushes a single part

1. var sb = string builder
2. sb push
   - Expected: sb.to_text() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push("hello")
expect(sb.to_text()).to_equal("hello")
```

</details>

#### pushes multiple parts

1. var sb = string builder
2. sb push
3. sb push
   - Expected: sb.to_text() equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push("Hello, ")
sb.push("World!")
expect(sb.to_text()).to_equal("Hello, World!")
```

</details>

#### push_line appends newline

1. var sb = string builder
2. sb push line
3. sb push
   - Expected: sb.to_text() equals `first\nsecond`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push_line("first")
sb.push("second")
expect(sb.to_text()).to_equal("first\nsecond")
```

</details>

### len

#### returns zero for empty

1. var sb = string builder
   - Expected: sb.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
expect(sb.len()).to_equal(0)
```

</details>

#### returns total character count

1. var sb = string builder
2. sb push
3. sb push
   - Expected: sb.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push("abc")
sb.push("de")
expect(sb.len()).to_equal(5)
```

</details>

### is_empty

#### true for new builder

1. var sb = string builder
   - Expected: sb.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
expect(sb.is_empty()).to_equal(true)
```

</details>

#### false after push

1. var sb = string builder
2. sb push
   - Expected: sb.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push("x")
expect(sb.is_empty()).to_equal(false)
```

</details>

### clear

#### clears all parts

1. var sb = string builder
2. sb push
3. sb clear
   - Expected: sb.is_empty() is true
   - Expected: sb.to_text() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sb = string_builder()
sb.push("data")
sb.clear()
expect(sb.is_empty()).to_equal(true)
expect(sb.to_text()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StringBuilder
- basic construction
- push and to_text
- len
- is_empty
- clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
