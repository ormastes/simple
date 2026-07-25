# Head Specification

> <details>

<!-- sdn-diagram:id=head_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=head_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

head_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=head_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Head Specification

## Scenarios

### head tool

#### line selection

#### gets first N lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "line1\nline2\nline3\nline4\nline5"
val result = head_lines(content, 3)
expect(result).to_equal("line1\nline2\nline3")
```

</details>

#### returns all lines when N exceeds count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "line1\nline2"
val result = head_lines(content, 10)
expect(result).to_equal("line1\nline2")
```

</details>

#### returns first line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "only\nsecond"
val result = head_lines(content, 1)
expect(result).to_equal("only")
```

</details>

#### byte selection

#### gets first N bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "hello world"
val result = head_bytes(content, 5)
expect(result).to_equal("hello")
```

</details>

#### returns all when N exceeds length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "hi"
val result = head_bytes(content, 100)
expect(result).to_equal("hi")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/head_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- head tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
