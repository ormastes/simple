# Text From Parts Specification

> <details>

<!-- sdn-diagram:id=text_from_parts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_from_parts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_from_parts_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_from_parts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text From Parts Specification

## Scenarios

### text_from_parts

#### joins parts into single string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts(["hello", " ", "world"])
expect(result).to_equal("hello world")
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts([])
expect(result).to_equal("")
```

</details>

#### handles single part

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts(["only"])
expect(result).to_equal("only")
```

</details>

#### joins multiple parts without separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts(["a", "b", "c", "d"])
expect(result).to_equal("abcd")
```

</details>

#### handles parts with newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts(["line1\n", "line2\n", "line3"])
expect(result).to_equal("line1\nline2\nline3")
```

</details>

#### handles empty string parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_from_parts(["", "hello", "", "world", ""])
expect(result).to_equal("helloworld")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_from_parts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text_from_parts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
