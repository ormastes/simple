# Formatter Specification

> <details>

<!-- sdn-diagram:id=formatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Specification

## Scenarios

### Formatter Integration

#### keeps test runner output format entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_test_runner_source("src/app/test_runner_new/test_runner_output.spl")

expect(source).to_contain("fn print_result(result: TestFileResult, format: OutputFormat)")
expect(source).to_contain("fn print_summary(result: TestRunResult, format: OutputFormat)")
```

</details>

#### keeps stats formatter entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table_source = read_test_runner_source("src/app/stats/formatter.spl")
val json_source = read_test_runner_source("src/app/stats/json_formatter.spl")

expect(table_source).to_contain("fn format_stats_table(stats: ProjectStats) -> text")
expect(json_source).to_contain("fn format_json(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/spec/formatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Formatter Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
