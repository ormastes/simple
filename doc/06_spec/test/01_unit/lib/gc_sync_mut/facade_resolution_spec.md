# Facade Resolution Specification

> <details>

<!-- sdn-diagram:id=facade_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=facade_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

facade_resolution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=facade_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Facade Resolution Specification

## Scenarios

### gc_sync_mut facade resolution

#### resolves pure helpers through the gc_async_mut backing family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = array_position([10, 20, 30], _1 == 20)
expect(idx).to_equal(1)
```

</details>

#### preserves pure helper behavior through the sync facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = array_find_or([1, 3, 5], _1 > 10, 99)
expect(found).to_equal(99)

val prefix = array_take_while([2, 4, 5, 6], _1 % 2 == 0)
expect(prefix).to_equal([2, 4])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_sync_mut/facade_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_sync_mut facade resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
