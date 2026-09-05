# Simple 2d Renderdoc Backend Equivalence Aggregate Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple 2d Renderdoc Backend Equivalence Aggregate Specification

## Scenarios

### Backend equivalence aggregate

#### rejects unavailable runtime and capture inputs without hiding rows

- Calibrate the aggregate fail-closed contract
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Calibrate the aggregate fail-closed contract")
val (_stdout, _stderr, code) = process_run(
    "/bin/sh",
    ["scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs", "--self-test"]
)
expect(code).to_equal(0)
expect(_stdout).to_contain("simple_renderdoc_aggregate_self_test_status=pass")
```

</details>

#### reports focused rows timing RSS blockers and requirement traceability

- Run the focused profile once
   - Exec capture: after_step
- Inspect every retained host and backend row
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: value_of(evidence, "simple_renderdoc_aggregate_profile") equals `focused`
- Require a pass or a typed nonempty blocker collection
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: code equals `0`
   - Expected: value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count") equals `0`
   - Expected: status equals `blocked`
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the focused profile once")
val root = "build/test-simple-2d-renderdoc-backend-equivalence"
val command = "BUILD_DIR=" + root + "/out REPORT_PATH=" + root +
    "/report.md sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=focused"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_be_less_than(2)

step("Inspect every retained host and backend row")
val evidence = file_read(root + "/out/evidence.env")
expect(value_of(evidence, "simple_renderdoc_aggregate_schema")).to_equal(
    "simple-renderdoc-aggregate-v1")
expect(value_of(evidence, "simple_renderdoc_aggregate_profile")).to_equal("focused")
expect(value_of(evidence, "simple_renderdoc_aggregate_row_count").to_i64()).to_be_greater_than(0)
expect(evidence).to_contain("_elapsed_ms=")
expect(evidence).to_contain("_max_rss_kb=")
expect(evidence).to_contain("_requirements=")
expect(evidence).to_contain("simple_renderdoc_aggregate_simpleos_simd_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_windows_d3d11_d3d12_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_macos_metal_status=")
expect(evidence).to_contain("simple_renderdoc_aggregate_physical_boards_status=")

step("Require a pass or a typed nonempty blocker collection")
val status = value_of(evidence, "simple_renderdoc_aggregate_status")
if status == "pass":
    expect(code).to_equal(0)
    expect(value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count")).to_equal("0")
else:
    expect(status).to_equal("blocked")
    expect(code).to_equal(1)
    expect(value_of(evidence, "simple_renderdoc_aggregate_profile_blocker_count").to_i64()).to_be_greater_than(0)
    expect(value_of(evidence, "simple_renderdoc_aggregate_blocker_keys").len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend equivalence aggregate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
