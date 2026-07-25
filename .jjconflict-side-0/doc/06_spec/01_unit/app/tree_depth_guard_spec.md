# Tree Depth Guard Specification

> <details>

<!-- sdn-diagram:id=tree_depth_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tree_depth_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tree_depth_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tree_depth_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tree Depth Guard Specification

## Scenarios

### tree depth guard

#### guards malformed depth values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/tree/main.spl") ?? ""

expect(source).to_contain("fn parse_tree_depth_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("max_depth = parse_tree_depth_or_default(arg[8:], max_depth)")
expect(source.contains("max_depth = arg[8:].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tree_depth_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tree depth guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
