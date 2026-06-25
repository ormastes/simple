# Spl Coverage Specification

> <details>

<!-- sdn-diagram:id=spl_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spl_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spl_coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spl_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spl Coverage Specification

## Scenarios

### Spl Coverage

#### keeps spl coverage CLI commands available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = spl_coverage_source()

expect(source).to_contain("fn print_help()")
expect(source).to_contain("fn cmd_dump(args: [text]) -> i64")
expect(source).to_contain("fn cmd_status() -> i64")
expect(source).to_contain("fn cmd_clear() -> i64")
expect(source).to_contain("fn main() -> i64")
expect(source).to_contain("SIMPLE_COVERAGE=1")
```

</details>

#### keeps coverage result model and check API available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = coverage_library_source()

expect(source).to_contain("struct FileResult:")
expect(source).to_contain("struct CoverageResult:")
expect(source).to_contain("fn _parse_coverage_file(content: text) -> [FileResult]")
expect(source).to_contain("fn _calculate_coverage(coverage_type: text, files: [FileResult]) -> f64")
expect(source).to_contain("fn check_coverage(coverage_type: text, pattern: text, minimum: f64 = 0.0, maximum: f64 = 100.0, minimum_check: bool = true) -> CoverageResult")
expect(source).to_contain("fn reload_coverage_data()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spl_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Spl Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
