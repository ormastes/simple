# Query Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=query_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Numeric Guard Specification

## Scenarios

### query cli numeric guard

#### guards malformed query coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = rt_file_read_text("src/app/cli/query.spl") ?? ""
val visibility = rt_file_read_text("src/app/cli/query_visibility_part1.spl") ?? ""

expect(query).to_contain("trimmed.to_int() ?? 0")
expect(visibility).to_contain("trimmed.to_int() ?? 0")
expect(visibility).to_contain("line_num: query_visibility_nonnegative_int_or_zero(args[2])")
expect(visibility).to_contain("col: query_visibility_nonnegative_int_or_zero(args[3])")
expect(visibility).to_contain("val token_line = query_visibility_nonnegative_int_or_zero(parts[0]) - 1")
expect(visibility).to_contain("val token_col = query_visibility_nonnegative_int_or_zero(parts[1])")
expect(visibility).to_contain("val token_len = query_visibility_nonnegative_int_or_zero(parts[2])")
expect(visibility).to_contain("line_num: query_visibility_nonnegative_int_or_zero(line_num_str)")
expect(visibility.contains("args[2].to_int()")).to_equal(false)
expect(visibility.contains("args[3].to_int()")).to_equal(false)
expect(visibility.contains("parts[0].to_int()")).to_equal(false)
expect(visibility.contains("parts[1].to_int()")).to_equal(false)
expect(visibility.contains("parts[2].to_int()")).to_equal(false)
expect(visibility.contains("line_num_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query cli numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
