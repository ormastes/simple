# Doc Coverage Dynamic Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=doc_coverage_dynamic_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doc_coverage_dynamic_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doc_coverage_dynamic_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doc_coverage_dynamic_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Coverage Dynamic Numeric Guard Specification

## Scenarios

### doc coverage dynamic stats numeric guard

#### guards shell count parsing with a fallback helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/stats/doc_coverage_dynamic.spl") ?? ""

expect(source).to_contain("fn dc_parse_count(output: text) -> i64:")
expect(source).to_contain("output.to_int() ?? 0")
expect(source).to_contain("dc_parse_count(dc_run_cmd(cmd))")
expect(source.contains("dc_run_cmd(cmd).to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/doc_coverage_dynamic_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- doc coverage dynamic stats numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
