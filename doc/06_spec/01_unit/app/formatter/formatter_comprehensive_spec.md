# Formatter Comprehensive Specification

> <details>

<!-- sdn-diagram:id=formatter_comprehensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=formatter_comprehensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

formatter_comprehensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=formatter_comprehensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formatter Comprehensive Specification

## Scenarios

### Formatter Comprehensive

#### keeps query formatting dispatchers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/query_formatting.spl") ?? ""

expect(source).to_contain("fn query_signature_help(symbol: text, file: text, line_num: i64, col: i64) -> i64")
expect(source).to_contain("fn query_document_formatting(file: text) -> i64")
expect(source).to_contain("fn query_ast_query(cmd_args: [text]) -> i64")
expect(source).to_contain("fn query_sem_query(cmd_args: [text]) -> i64")
expect(source).to_contain("fn query_query_schema(cmd_args: [text]) -> i64")
```

</details>

#### keeps stats formatting helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/stats/formatter.spl") ?? ""

expect(source).to_contain("fn percent(part: i64, total: i64) -> text")
expect(source).to_contain("fn format_stats_table(stats: ProjectStats) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/formatter/formatter_comprehensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Formatter Comprehensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
