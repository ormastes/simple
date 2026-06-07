# Database Feature Utils Specification

> 1. check

<!-- sdn-diagram:id=database_feature_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_feature_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_feature_utils_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_feature_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Feature Utils Specification

## Scenarios

### Database Feature Utils

#### parses attribute lists

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modes = parse_attr_list("modes(\"pure\", \"hybrid\")", "modes")
check(modes.len() == 2)
check(modes[0] == "pure")
check(modes[1] == "hybrid")
```

</details>

#### extracts quoted names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(extract_quoted_string("describe \"My Feature\":") == "My Feature")
```

</details>

#### extracts categories from feature paths

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(extract_category_from_path("test/system/features/control_flow/loops_spec.spl") == "control_flow")
check(extract_category_from_path("spec.spl") == "uncategorized")
```

</details>

#### compares feature ids semantically

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(compare_feature_id("1.2", "1.10") < 0)
check(compare_feature_id("1.10.1", "1.2.20") > 0)
check(compare_feature_id("alpha", "beta") < 0)
```

</details>

#### parses spipe metadata from a temp file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = write_spec("metadata", """
```

</details>

### My Feature

### Auto ID Feature

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | feature_001 |
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_feature_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Database Feature Utils
- My Feature
- Auto ID Feature

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
