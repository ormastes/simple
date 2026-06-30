# Option Utils Specification

> <details>

<!-- sdn-diagram:id=option_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Utils Specification

## Scenarios

### Option Utils

#### uses nil coalescing fallback for absent values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val configured = nil
val effective = configured ?? "default"
expect effective == "default"
```

</details>

#### preserves present option values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val configured = Some("explicit")
val effective = configured ?? "default"
expect effective == "explicit"
```

</details>

#### matches Some values

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = Some(42)
val rendered = match value:
    Some(n): "value={n}"
    nil: "missing"
expect rendered == "value=42"
```

</details>

#### matches nil values

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = nil
val rendered = match value:
    Some(n): "value={n}"
    nil: "missing"
expect rendered == "missing"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/option_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Option Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
