# Count Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=count_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=count_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

count_numeric_guard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=count_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Count Numeric Guard Specification

## Scenarios

### svim count numeric guard

#### falls back when a normal command count is too large

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = svim_parse_normal_command("999999999999999999999999999999999999999999999999j")
expect cmd.name to_equal "move-down"
expect cmd.count to_equal 1
```

</details>

#### falls back when an operator motion count is too large

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = svim_parse_normal_command("d999999999999999999999999999999999999999999999999w")
expect cmd.name to_equal "delete-motion"
expect cmd.count to_equal 1
expect cmd.payload to_equal "word"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/count_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svim count numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
