# Generic Repro Specification

> 1. values push

<!-- sdn-diagram:id=generic_repro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_repro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_repro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_repro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Repro Specification

## Scenarios

### generic syntax repros

#### dispatches methods through a generic type alias

1. values push
   - Expected: values.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = ReproIntVec(items: [])
values.push(10)
expect(values.length()).to_equal(1)
```

</details>

#### parses generic instance method calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = ReproBox<i64>(value: 42)
expect(box.get()).to_equal(42)
```

</details>

#### parses explicit generic function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(repro_identity<i64>(42)).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/language/generic_repro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generic syntax repros

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
