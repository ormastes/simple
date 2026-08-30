# Query Tokens Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=query_tokens_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_tokens_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_tokens_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_tokens_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Tokens Numeric Guard Specification

## Scenarios

### query tokens numeric guard

#### defaults malformed token range coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_tokens.spl") ?? ""

expect(source).to_contain("fn query_tokens_nonnegative_int_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("val start_line = query_tokens_nonnegative_int_or_default(start_line_str, 1)")
expect(source).to_contain("var end_line = query_tokens_nonnegative_int_or_default(end_line_str, 0)")
expect(source.contains("start_line_str.to_int()")).to_equal(false)
expect(source.contains("end_line_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_tokens_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- query tokens numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
