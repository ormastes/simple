# Gc Stats Specification

> <details>

<!-- sdn-diagram:id=gc_stats_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_stats_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_stats_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_stats_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gc Stats Specification

## Scenarios

### nogc_async_mut GC stats

#### returns zero survival rate for empty stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GcStats.new().survival_rate()).to_equal(0.0)
```

</details>

#### guards freed count above allocated count

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = GcStats(
    collections: 0,
    objects_allocated: 1,
    objects_freed: 2,
    bytes_allocated: 0,
    bytes_freed: 0,
    young_collections: 0,
    full_collections: 0,
    total_pause_time: 0,
    last_pause_time: 0
)
expect(stats.survival_rate()).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gc_stats_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut GC stats

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
