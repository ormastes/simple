# Coverage Threshold Specification

> <details>

<!-- sdn-diagram:id=coverage_threshold_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_threshold_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_threshold_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_threshold_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Threshold Specification

## Scenarios

### Coverage Threshold

#### keeps test runner coverage data model available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/test_runner_new/test_runner_coverage.spl") ?? ""

expect(source).to_contain("struct FileCoverage")
expect(source).to_contain("struct CoverageData")
expect(source).to_contain("fn parse_coverage_sdn(sdn: text) -> CoverageData")
```

</details>

#### keeps coverage threshold and sorting helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/test_runner_new/test_runner_coverage.spl") ?? ""

expect(source).to_contain("fn sort_files_by_coverage(files: [FileCoverage]) -> [FileCoverage]")
expect(source).to_contain("fn check_coverage_threshold(data: CoverageData, threshold: i64) -> bool")
expect(source).to_contain("fn get_coverage_threshold() -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/coverage_threshold_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Coverage Threshold

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
