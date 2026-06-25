# Main Part1 Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=main_part1_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_part1_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_part1_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_part1_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Part1 Numeric Guard Specification

## Scenarios

### main cli numeric guard

#### guards malformed global numeric flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/main_part1.spl") ?? ""

expect(source).to_contain("fn parse_cli_nonnegative_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("jit_threshold = parse_cli_nonnegative_or_default(val_str, jit_threshold)")
expect(source).to_contain("jit_threshold = parse_cli_nonnegative_or_default(args[i], jit_threshold)")
expect(source).to_contain("max_recursion_depth = parse_cli_nonnegative_or_default(val_str, max_recursion_depth)")
expect(source).to_contain("max_recursion_depth = parse_cli_nonnegative_or_default(args[i], max_recursion_depth)")
expect(source).to_contain("timeout_secs = parse_cli_nonnegative_or_default(val_str, timeout_secs)")
expect(source).to_contain("timeout_secs = parse_cli_nonnegative_or_default(args[i], timeout_secs)")
expect(source).to_contain("execution_limit = parse_cli_nonnegative_or_default(val_str, execution_limit)")
expect(source).to_contain("execution_limit = parse_cli_nonnegative_or_default(args[i], execution_limit)")
expect(source.contains("val_str.to_int()")).to_equal(false)
expect(source.contains("args[i].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/main_part1_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- main cli numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
