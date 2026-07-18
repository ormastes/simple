# Statistics Specification

> <details>

<!-- sdn-diagram:id=statistics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=statistics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

statistics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=statistics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Statistics Specification

## Scenarios

### Statistics

#### keeps public coverage statistics APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/doc/public_check/statistics.spl") ?? ""

expect(source).to_contain("struct PublicCoverageStats")
expect(source).to_contain("fn calculate_public_coverage(module_path: text, exports: [text], documented: [text]) -> PublicCoverageStats")
expect(source).to_contain("fn format_coverage_report(stats: PublicCoverageStats) -> text")
expect(source).to_contain("fn coverage_to_json(stats: PublicCoverageStats) -> text")
expect(source).to_contain("fn meets_threshold(stats: PublicCoverageStats, threshold: f64) -> bool")
```

</details>

#### keeps MDSOC coverage statistics APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/doc/public_check/statistics.spl") ?? ""

expect(source).to_contain("struct MdsocCoverageStats")
expect(source).to_contain("fn calculate_mdsoc_coverage")
expect(source).to_contain("fn format_mdsoc_report(stats: MdsocCoverageStats) -> text")
expect(source).to_contain("fn mdsoc_stats_to_json(stats: MdsocCoverageStats) -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc/public_check/statistics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Statistics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
