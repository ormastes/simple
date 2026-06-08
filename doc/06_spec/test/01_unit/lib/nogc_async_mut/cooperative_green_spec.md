# Cooperative Green Specification

> <details>

<!-- sdn-diagram:id=cooperative_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cooperative_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cooperative_green_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cooperative_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cooperative Green Specification

## Scenarios

### Cooperative green facade

#### keeps queued work on the cooperative scheduler

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = cooperative_green_ready_count()
val handle = cooperative_green_spawn(cooperative_green_value_5)
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(5)
```

</details>

#### runs multiple cooperative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = cooperative_green_spawn(cooperative_green_value_5)
val h2 = cooperative_green_spawn(cooperative_green_value_13)
val ran = cooperative_green_run_all()
expect(ran >= 2).to_equal(true)
expect(h1.join()).to_equal(5)
expect(h2.join()).to_equal(13)
```

</details>

#### supports direct value scheduling for profile smoke workloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = cooperative_green_spawn_value(21)
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.join()).to_equal(21)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Cooperative green facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
