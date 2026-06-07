# Persistent Collections Native Specification

> <details>

<!-- sdn-diagram:id=persistent_collections_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_collections_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_collections_native_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_collections_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Collections Native Specification

## Scenarios

### gc_async_immut persistent collections native

#### preserves list snapshots through the root facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentList.of([1, 2, 3])
val extended = base.prepend(0)

expect(base.len()).to_equal(3)
expect(base.head()).to_equal(1)
expect(extended.len()).to_equal(4)
expect(extended.head()).to_equal(0)
expect(extended.tail().head()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/persistent_collections_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut persistent collections native

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
