# Feature Request Rows Specification

> <details>

<!-- sdn-diagram:id=feature_request_rows_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_request_rows_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_request_rows_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_request_rows_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Request Rows Specification

## Scenarios

### feature request row writer

#### quotes comma-containing descriptions for canonical feature_db rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = feature_request_row_line(FeatureRequestRow(
    id: "FR-TEST-0001",
    group: "tracking",
    component: "tracking",
    title: "Quoted row",
    description: "needs comma, preserved",
    priority: "P1",
    source_file: "doc/08_tracking/feature/source.md",
    plan: "",
    architecture: "",
    design: "",
    system_spec: "",
    spec_doc: "",
    guide: "",
    created_at: "2026-06-28",
    updated_at: "2026-06-28"
))

expect(row).to_contain("\"needs comma, preserved\"")
expect(row).to_contain("\"FR-TEST-0001\"")
expect(row).to_end_with("true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/feature_request_rows_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- feature request row writer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
