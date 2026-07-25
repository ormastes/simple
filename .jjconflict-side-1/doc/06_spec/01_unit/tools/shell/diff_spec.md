# Diff Specification

> <details>

<!-- sdn-diagram:id=diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Specification

## Scenarios

### diff tool

#### identical files

#### returns no differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "line1\nline2\nline3"
val b = "line1\nline2\nline3"
expect(a == b).to_equal(true)
```

</details>

#### different files

#### detects changed lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "line1\nline2\nline3"
val b = "line1\nchanged\nline3"
val lines_a = a.split("\n")
val lines_b = b.split("\n")
expect(lines_a[1] != lines_b[1]).to_equal(true)
```

</details>

#### detects added lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "line1\nline2"
val b = "line1\nline2\nline3"
val lines_a = a.split("\n")
val lines_b = b.split("\n")
expect(lines_b.len()).to_be_greater_than(lines_a.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diff tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
