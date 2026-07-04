# Coverage Ffi Specification

> <details>

<!-- sdn-diagram:id=coverage_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Ffi Specification

## Scenarios

### Coverage Ffi

#### keeps source coverage FFI wrappers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/io/coverage_simple.spl") ?? ""

expect(source).to_contain("fn coverage_enabled() -> bool")
expect(source).to_contain("fn coverage_clear()")
expect(source).to_contain("fn coverage_decision(file: text, line: i64, decision_id: i64, taken: bool)")
expect(source).to_contain("fn coverage_condition(file: text, line: i64, condition_id: i64, result: bool)")
expect(source).to_contain("fn coverage_path(file: text, line: i64, path_id: i64)")
expect(source).to_contain("fn coverage_report() -> text")
```

</details>

#### keeps coverage statistics parser available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/io/coverage_simple.spl") ?? ""

expect(source).to_contain("struct CoverageStats")
expect(source).to_contain("fn parse_coverage_stats(sdn: text) -> CoverageStats")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/coverage_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Coverage Ffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
