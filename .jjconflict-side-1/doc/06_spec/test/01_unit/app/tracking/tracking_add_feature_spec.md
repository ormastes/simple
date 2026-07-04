# Tracking Add Feature Specification

> <details>

<!-- sdn-diagram:id=tracking_add_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tracking_add_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tracking_add_feature_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tracking_add_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tracking Add Feature Specification

## Scenarios

### tracking add-feature command

#### routes requested feature rows through the feature database owner API

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = tracking_source()

expect(source).to_contain("add-feature")
expect(source).to_contain("FeatureRequestRow(")
expect(source).to_contain("add_feature_request_row(FEATURE_DB_PATH, feature)")
```

</details>

#### exposes traceability flags for canonical requested rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = tracking_source()

expect(source).to_contain("--source=<path>")
expect(source).to_contain("--plan=<path>")
expect(source).to_contain("--architecture=<path>")
expect(source).to_contain("--design=<path>")
expect(source).to_contain("--system-spec=<path>")
expect(source).to_contain("--spec-doc=<path>")
expect(source).to_contain("--guide=<path>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tracking/tracking_add_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tracking add-feature command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
