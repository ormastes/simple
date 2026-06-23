# Stats Dynamic Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=stats_dynamic_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stats_dynamic_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stats_dynamic_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stats_dynamic_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stats Dynamic Numeric Guard Specification

## Scenarios

### compiler dynamic stats numeric guard

#### guards shell count parsing with fallback helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = rt_file_read_text("src/compiler/90.tools/stats/dynamic.spl") ?? ""
val doc_stats = rt_file_read_text("src/compiler/90.tools/stats/doc_coverage_dynamic.spl") ?? ""

expect(stats).to_contain("fn parse_count(output: text) -> i64:")
expect(stats).to_contain("output.to_int() ?? 0")
expect(stats).to_contain("parse_count(run_cmd(cmd))")
expect(stats.contains("run_cmd(cmd).to_int()")).to_equal(false)
expect(doc_stats).to_contain("fn dc_parse_count(output: text) -> i64:")
expect(doc_stats).to_contain("dc_parse_count(dc_run_cmd(cmd))")
expect(doc_stats.contains("dc_run_cmd(cmd).to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/stats_dynamic_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compiler dynamic stats numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
