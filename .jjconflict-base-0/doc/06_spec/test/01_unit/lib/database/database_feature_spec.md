# Database Feature Specification

> <details>

<!-- sdn-diagram:id=database_feature_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_feature_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_feature_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_feature_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Feature Specification

## Scenarios

### DatabaseFeature

#### keeps feature database construction and row conversion available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_database_source()

expect(source).to_contain("fn load_feature_database(path: text) -> FeatureDatabase?")
expect(source).to_contain("fn create_feature_database(path: text) -> FeatureDatabase")
expect(source).to_contain("fn feature_to_row(feature: Feature) -> SdnRow")
expect(source).to_contain("struct FeatureRequestRow:")
expect(source).to_contain("fn feature_request_to_row(feature: FeatureRequestRow) -> SdnRow")
expect(source).to_contain("me add_feature_request(feature: FeatureRequestRow) -> bool")
expect(source).to_contain("class FeatureDatabase:")
```

</details>

#### keeps feature query and status APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_database_source()

expect(source).to_contain("fn get_feature(id: text) -> Feature?")
expect(source).to_contain("fn all_features() -> [Feature]")
expect(source).to_contain("fn features_by_category(category: text) -> [Feature]")
expect(source).to_contain("fn features_by_status(status: FeatureStatus) -> [Feature]")
expect(source).to_contain("fn features_by_mode_status(mode: FeatureMode, status: FeatureStatus) -> [Feature]")
```

</details>

#### keeps validation and status mapping available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_database_source()

expect(source).to_contain("fn validate() -> [DbIssue]")
expect(source).to_contain("fn status_to_string(status: FeatureStatus) -> text")
expect(source).to_contain("fn parse_status(s: text) -> FeatureStatus")
expect(source).to_contain("\"request\": FeatureStatus.Planned")
expect(source).to_contain("\"current\": FeatureStatus.InProgress")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_feature_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DatabaseFeature

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
