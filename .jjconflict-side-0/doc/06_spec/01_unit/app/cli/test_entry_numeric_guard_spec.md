# Test Entry Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=test_entry_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_entry_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_entry_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_entry_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Entry Numeric Guard Specification

## Scenarios

### test entry numeric guard

#### guards malformed depth and limit values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/test_entry.spl") ?? ""

expect(source).to_contain("fn parse_test_entry_nonnegative_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("val depth = parse_test_entry_nonnegative_or_default(depth_str, 0)")
expect(source).to_contain("val depth = parse_test_entry_nonnegative_or_default(arg[21:], 0)")
expect(source).to_contain("val secs = parse_test_entry_nonnegative_or_default(arg[10:], 0)")
expect(source).to_contain("val limit = parse_test_entry_nonnegative_or_default(arg[18:], 0)")
expect(source.contains("depth_str.to_int()")).to_equal(false)
expect(source.contains("arg[21:].to_int()")).to_equal(false)
expect(source.contains("arg[10:].to_int()")).to_equal(false)
expect(source.contains("arg[18:].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/test_entry_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test entry numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
