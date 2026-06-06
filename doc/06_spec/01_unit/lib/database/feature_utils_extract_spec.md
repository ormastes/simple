# Feature Utils Extract Specification

> <details>

<!-- sdn-diagram:id=feature_utils_extract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_utils_extract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_utils_extract_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_utils_extract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Utils Extract Specification

## Scenarios

### Feature Utils Ext

#### keeps SPipe metadata extraction helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_utils_source()

expect(source).to_contain("fn parse_spipe_metadata(file_path: text) -> [SPipeItem]")
expect(source).to_contain("fn parse_attr_list(line: text, attr_name: text) -> [text]")
expect(source).to_contain("fn extract_quoted_string(line: text) -> text")
expect(source).to_contain("fn extract_category_from_path(file_path: text) -> text")
```

</details>

#### keeps semantic feature sorting helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = feature_utils_source()

expect(source).to_contain("fn to_int_or(s: text, default: i64) -> i64")
expect(source).to_contain("fn compare_feature_id(a: text, b: text) -> i64")
expect(source).to_contain("fn sort_features_by_id(features: [Feature]) -> [Feature]")
expect(source).to_contain("fn merge_features(left: [Feature], right: [Feature]) -> [Feature]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/feature_utils_extract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Feature Utils Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
