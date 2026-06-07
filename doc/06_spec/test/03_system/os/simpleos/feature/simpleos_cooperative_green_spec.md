# SimpleOS Cooperative Green System Contract

> This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

<!-- sdn-diagram:id=simpleos_cooperative_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_cooperative_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_cooperative_green_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_cooperative_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Cooperative Green System Contract

This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-cooperative |
| Category | SimpleOS / Concurrency |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves that the implemented cooperative-green API remains
usable in the SimpleOS feature lane while preserving its explicit semantics: it
queues logical work on the current carrier and does not claim CPU-parallel M:N
execution.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### SimpleOS cooperative green contract

#### queues logical green work without marking it done before the carrier runs

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = cooperative_green_ready_count()
val handle = cooperative_green_spawn(simpleos_cooperative_green_value_3)

expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(3)
```

</details>

#### runs all queued cooperative work on the current carrier

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = cooperative_green_ready_count()
val h1 = cooperative_green_spawn(simpleos_cooperative_green_value_3)
val h2 = cooperative_green_spawn(simpleos_cooperative_green_value_8)

expect(cooperative_green_ready_count()).to_equal(before + 2)
val ran = cooperative_green_run_all()

expect(ran >= 2).to_equal(true)
expect(h1.join()).to_equal(3)
expect(h2.join()).to_equal(8)
```

</details>

#### supports direct value scheduling used by profile fanout rows

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = cooperative_green_ready_count()
val handle = cooperative_green_spawn_value(21)

expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
expect(cooperative_green_run_one()).to_equal(true)
expect(handle.join()).to_equal(21)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
