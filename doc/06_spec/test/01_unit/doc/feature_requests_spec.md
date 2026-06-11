# Feature Requests Specification

> 1. expect content contains

<!-- sdn-diagram:id=feature_requests_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_requests_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_requests_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_requests_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Requests Specification

## Scenarios

### features

### doc/TODO.md contains interpreter feature requests

#### AC-4: TODO.md contains FR-INTERP-001 (me fn mutation loss)

1. expect content contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-001") == true
```

</details>

#### AC-4: TODO.md contains FR-INTERP-002 (deeply nested assignment)

1. expect content contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-002") == true
```

</details>

#### AC-4: FR-INTERP-001 entry mentions me fn or mutation

1. expect content contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-001") == true
```

</details>

#### AC-4: FR-INTERP-002 entry mentions nested or assignment

1. expect content contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file_text("doc/TODO.md")
expect content.contains("FR-INTERP-002") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/doc/feature_requests_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- features
- doc/TODO.md contains interpreter feature requests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
