# Comparison Failure Report Specification

> <details>

<!-- sdn-diagram:id=comparison_failure_report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=comparison_failure_report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

comparison_failure_report_spec -> std
comparison_failure_report_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=comparison_failure_report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comparison Failure Report Specification

## Scenarios

### wm_compare comparison failure report

#### preserves capture failure before metadata layout or pixel checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = comparison_failure_report(
    "chrome", "simple",
    false, true,
    true,
    "layout_match",
    true,
    "Initialized"
)
expect(report.capture_status).to_equal("capture_failed")
expect(report.metadata_status).to_equal("not_evaluated")
expect(report.structural_status).to_equal("not_evaluated")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.accepted).to_equal(false)
```

</details>

#### separates metadata mismatch from pixel mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    false,
    "layout_match",
    false,
    "Initialized"
)
expect(report.capture_status).to_equal("ok")
expect(report.metadata_status).to_equal("metadata_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.primary_status).to_equal("metadata_mismatch")
```

</details>

#### separates structural geometry mismatch from pixel mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = comparison_failure_report(
    "tui", "gui",
    true, true,
    true,
    "layout_mismatch",
    true,
    "Initialized"
)
expect(report.structural_status).to_equal("layout_mismatch")
expect(report.pixel_status).to_equal("not_evaluated")
expect(report.primary_status).to_equal("layout_mismatch")
expect(report.accepted).to_equal(false)
```

</details>

#### reports exact pixel mismatch after valid capture metadata and layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    true,
    "layout_match",
    false,
    "Initialized"
)
expect(report.capture_status).to_equal("ok")
expect(report.metadata_status).to_equal("ok")
expect(report.structural_status).to_equal("layout_match")
expect(report.pixel_status).to_equal("exact_mismatch")
expect(report.primary_status).to_equal("exact_mismatch")
expect(report.exact_required).to_equal(true)
expect(report.perceptual_diagnostic_only).to_equal(true)
expect(report.tolerance_acceptance_allowed).to_equal(false)
```

</details>

#### keeps backend unavailability separate from comparison acceptance

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = comparison_failure_report(
    "chrome", "simple",
    true, true,
    true,
    "layout_match",
    true,
    "Unavailable"
)
expect(report.accepted).to_equal(true)
expect(report.backend_status).to_equal("backend_unavailable")
expect(report.primary_status).to_equal("backend_unavailable")
val sdn = comparison_failure_report_sdn(report)
expect(sdn).to_contain("capture_status: \"ok\"")
expect(sdn).to_contain("pixel_status: \"exact_match\"")
expect(sdn).to_contain("backend_status: \"backend_unavailable\"")
expect(sdn).to_contain("acceptance_policy: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/comparison_failure_report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare comparison failure report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
