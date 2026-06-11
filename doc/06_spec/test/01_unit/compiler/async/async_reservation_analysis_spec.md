# Async Reservation Analysis Specification

> <details>

<!-- sdn-diagram:id=async_reservation_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_reservation_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_reservation_analysis_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_reservation_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Reservation Analysis Specification

## Scenarios

### get_task_reserve lookup

#### returns count for existing path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = make_reservation("uart_rx", ["NetRes.pkt_pool", "NetRes.rxq.entries"], [2, 1], 1)
expect(get_task_reserve(task, "NetRes.pkt_pool")).to_equal(2)
expect(get_task_reserve(task, "NetRes.rxq.entries")).to_equal(1)
```

</details>

#### returns zero for missing path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = make_reservation("uart_rx", ["NetRes.pkt_pool"], [2], 1)
expect(get_task_reserve(task, "NetRes.stats")).to_equal(0)
```

</details>

#### returns zero for empty reserves

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = make_empty_reservation("idle_task", 1)
expect(get_task_reserve(task, "NetRes.pkt_pool")).to_equal(0)
```

</details>

### Single resource demand

#### passes when demand within capacity

- make reservation
- make reservation
   - Expected: result.has_errors is false
   - Expected: result.passed_checks equals `1`
   - Expected: result.total_checks equals `1`
   - Expected: result.demands[0].total_demand equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 8)
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool"], [1], 2),
    make_reservation("parser", ["NetRes.pkt_pool"], [1], 3)
]
val result = verify_reservations([leaf], tasks)
expect(result.has_errors).to_equal(false)
expect(result.passed_checks).to_equal(1)
expect(result.total_checks).to_equal(1)
# demand = 1*2 + 1*3 = 5 <= 8
expect(result.demands[0].total_demand).to_equal(5)
```

</details>

#### passes when demand equals capacity

- make reservation
- make reservation
   - Expected: result.has_errors is false
   - Expected: result.demands[0].total_demand equals `8`
   - Expected: result.demands[0].overflow is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 8)
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool"], [2], 2),
    make_reservation("parser", ["NetRes.pkt_pool"], [2], 2)
]
val result = verify_reservations([leaf], tasks)
expect(result.has_errors).to_equal(false)
# demand = 2*2 + 2*2 = 8 == 8
expect(result.demands[0].total_demand).to_equal(8)
expect(result.demands[0].overflow).to_equal(false)
```

</details>

#### errors when demand exceeds capacity

- make reservation
- make reservation
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands[0].total_demand equals `7`
   - Expected: result.demands[0].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 4)
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool"], [3], 2),
    make_reservation("parser", ["NetRes.pkt_pool"], [1], 1)
]
val result = verify_reservations([leaf], tasks)
expect(result.has_errors).to_equal(true)
expect(result.passed_checks).to_equal(0)
# demand = 3*2 + 1*1 = 7 > 4
expect(result.demands[0].total_demand).to_equal(7)
expect(result.demands[0].overflow).to_equal(true)
```

</details>

### Multi-resource checks

#### passes when all resources within capacity

- make leaf
- make leaf
- make reservation
   - Expected: result.has_errors is false
   - Expected: result.passed_checks equals `2`
   - Expected: result.total_checks equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [
    make_leaf("NetRes.pkt_pool", "PktBuf", 8),
    make_leaf("NetRes.rxq.entries", "RxEntry", 8)
]
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool", "NetRes.rxq.entries"], [1, 1], 2)
]
val result = verify_reservations(leaves, tasks)
expect(result.has_errors).to_equal(false)
expect(result.passed_checks).to_equal(2)
expect(result.total_checks).to_equal(2)
```

</details>

#### errors when one resource overflows

- make leaf
- make leaf
- make reservation
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `1`
   - Expected: result.demands[0].overflow is false
   - Expected: result.demands[1].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [
    make_leaf("NetRes.pkt_pool", "PktBuf", 8),
    make_leaf("NetRes.rxq.waiters", "Waiter", 2)
]
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool", "NetRes.rxq.waiters"], [1, 1], 3)
]
val result = verify_reservations(leaves, tasks)
expect(result.has_errors).to_equal(true)
# pkt_pool: 1*3=3 <= 8 OK, waiters: 1*3=3 > 2 OVERFLOW
expect(result.passed_checks).to_equal(1)
expect(result.demands[0].overflow).to_equal(false)
expect(result.demands[1].overflow).to_equal(true)
```

</details>

#### errors when all resources overflow

- make leaf
- make leaf
- make reservation
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands[0].overflow is true
   - Expected: result.demands[1].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [
    make_leaf("pool_a", "A", 2),
    make_leaf("pool_b", "B", 3)
]
val tasks = [
    make_reservation("task1", ["pool_a", "pool_b"], [2, 2], 2)
]
val result = verify_reservations(leaves, tasks)
expect(result.has_errors).to_equal(true)
expect(result.passed_checks).to_equal(0)
# pool_a: 2*2=4 > 2, pool_b: 2*2=4 > 3
expect(result.demands[0].overflow).to_equal(true)
expect(result.demands[1].overflow).to_equal(true)
```

</details>

### Per-task breakdown

#### tracks contributor names

- make reservation
- make reservation
   - Expected: demand.contributor_names.len() equals `2`
   - Expected: demand.contributor_names[0] equals `uart_rx`
   - Expected: demand.contributor_names[1] equals `parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 100)
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool"], [2], 3),
    make_reservation("parser", ["NetRes.pkt_pool"], [4], 2)
]
val result = verify_reservations([leaf], tasks)
val demand = result.demands[0]
expect(demand.contributor_names.len()).to_equal(2)
expect(demand.contributor_names[0]).to_equal("uart_rx")
expect(demand.contributor_names[1]).to_equal("parser")
```

</details>

#### tracks contributor amounts

- make reservation
- make reservation
   - Expected: demand.contributor_amounts[0] equals `6`
   - Expected: demand.contributor_amounts[1] equals `8`
   - Expected: demand.total_demand equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 100)
val tasks = [
    make_reservation("uart_rx", ["NetRes.pkt_pool"], [2], 3),
    make_reservation("parser", ["NetRes.pkt_pool"], [4], 2)
]
val result = verify_reservations([leaf], tasks)
val demand = result.demands[0]
# uart_rx: 2*3=6, parser: 4*2=8
expect(demand.contributor_amounts[0]).to_equal(6)
expect(demand.contributor_amounts[1]).to_equal(8)
expect(demand.total_demand).to_equal(14)
```

</details>

### Group-aware instances

#### uses exact spawn counts not declared instances

- make reservation
   - Expected: result.has_errors is false
   - Expected: result.demands[0].total_demand equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Task declared with instances=4, but only spawned 2 times
val leaf = make_leaf("pool", "Unit", 5)
val tasks = [
    make_reservation("task_a", ["pool"], [2], 2)
]
val result = verify_reservations([leaf], tasks)
# demand = 2*2 = 4 <= 5 (uses instances=2, not declared max)
expect(result.has_errors).to_equal(false)
expect(result.demands[0].total_demand).to_equal(4)
```

</details>

#### would overflow with declared instances but not with actual

- make reservation
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If instances were 4 (declared), demand would be 2*4=8 > 5
# But actual spawn count is 2, so demand = 2*2=4 <= 5
val leaf = make_leaf("pool", "Unit", 5)
val tasks = [
    make_reservation("task_a", ["pool"], [2], 2)
]
val result = verify_reservations([leaf], tasks)
expect(result.has_errors).to_equal(false)
```

</details>

### Zero reserves

#### task with no reserves contributes nothing

- make empty reservation
- make reservation
   - Expected: result.demands[0].total_demand equals `2`
   - Expected: result.demands[0].contributor_names.len() equals `1`
   - Expected: result.demands[0].contributor_names[0] equals `worker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("pool", "Unit", 4)
val tasks = [
    make_empty_reservation("idle_task", 3),
    make_reservation("worker", ["pool"], [1], 2)
]
val result = verify_reservations([leaf], tasks)
# Only worker contributes: 1*2=2
expect(result.demands[0].total_demand).to_equal(2)
expect(result.demands[0].contributor_names.len()).to_equal(1)
expect(result.demands[0].contributor_names[0]).to_equal("worker")
```

</details>

#### resource with no reservers has zero demand

- make reservation
   - Expected: result.demands[0].total_demand equals `0`
   - Expected: result.demands[0].overflow is false
   - Expected: result.demands[0].contributor_names.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("unused_pool", "Unit", 4)
val tasks = [
    make_reservation("worker", ["other_pool"], [1], 2)
]
val result = verify_reservations([leaf], tasks)
expect(result.demands[0].total_demand).to_equal(0)
expect(result.demands[0].overflow).to_equal(false)
expect(result.demands[0].contributor_names.len()).to_equal(0)
```

</details>

### Edge cases

#### handles empty leaves list

- make reservation
   - Expected: result.has_errors is false
   - Expected: result.total_checks equals `0`
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tasks = [
    make_reservation("worker", ["pool"], [1], 2)
]
val result = verify_reservations([], tasks)
expect(result.has_errors).to_equal(false)
expect(result.total_checks).to_equal(0)
expect(result.passed_checks).to_equal(0)
expect(result.demands.len()).to_equal(0)
```

</details>

#### handles empty tasks list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [make_leaf("pool", "Unit", 4)]
val result = verify_reservations(leaves, [])
expect(result.has_errors).to_equal(false)
expect(result.total_checks).to_equal(1)
expect(result.passed_checks).to_equal(1)
expect(result.demands[0].total_demand).to_equal(0)
```

</details>

### Data structure construction

#### creates ResourceLeaf correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 8)
expect(leaf.path).to_equal("NetRes.pkt_pool")
expect(leaf.unit_name).to_equal("PktBuf")
expect(leaf.cap).to_equal(8)
```

</details>

#### creates TaskReservation correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val task = make_reservation("uart_rx", ["pool_a", "pool_b"], [2, 3], 4)
expect(task.task_name).to_equal("uart_rx")
expect(task.reserve_paths.len()).to_equal(2)
expect(task.reserve_counts.len()).to_equal(2)
expect(task.instances).to_equal(4)
expect(task.reserve_paths[0]).to_equal("pool_a")
expect(task.reserve_counts[1]).to_equal(3)
```

</details>

#### creates ReservationDemand via compute_demand

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaf = make_leaf("pool", "Unit", 10)
val tasks = [make_reservation("t1", ["pool"], [3], 2)]
val demand = compute_demand(leaf, tasks)
expect(demand.resource_path).to_equal("pool")
expect(demand.total_demand).to_equal(6)
expect(demand.cap).to_equal(10)
expect(demand.overflow).to_equal(false)
```

</details>

### Reservation formatting

#### formats passing result

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [make_leaf("pool", "Unit", 10)]
val tasks = [make_reservation("t1", ["pool"], [1], 2)]
val result = verify_reservations(leaves, tasks)
val output = format_reservation_result(result)
expect(output).to_contain("Reservation Verification: pass")
expect(output).to_contain("1/1 resources OK")
expect(output).to_contain("pool")
```

</details>

#### formats failing result with overflow details

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val leaves = [make_leaf("pool", "Unit", 2)]
val tasks = [make_reservation("t1", ["pool"], [3], 2)]
val result = verify_reservations(leaves, tasks)
val output = format_reservation_result(result)
expect(output).to_contain("Reservation Verification: FAIL")
expect(output).to_contain("0/1 resources OK")
expect(output).to_contain("OVERFLOW")
expect(output).to_contain("reservation overflow")
```

</details>

### End-to-end: spec Section 11 NetRes scenario

#### validates full NetRes resource set

- make leaf
- make leaf
- make leaf
- make leaf
   - Expected: result.has_errors is false
   - Expected: result.total_checks equals `4`
   - Expected: result.passed_checks equals `4`
   - Expected: result.demands[0].total_demand equals `1`
   - Expected: result.demands[1].total_demand equals `1`
   - Expected: result.demands[2].total_demand equals `1`
   - Expected: result.demands[3].total_demand equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Resources from spec
val leaves = [
    make_leaf("NetRes.pkt_pool", "PktBuf", 8),
    make_leaf("NetRes.rxq.entries", "RxEntry", 8),
    make_leaf("NetRes.rxq.waiters", "Waiter", 2),
    make_leaf("NetRes.stats", "StatSlot", 64)
]

# Tasks: uart_rx (1 instance), parser (1 instance)
val tasks = [
    make_reservation(
        "uart_rx",
        ["NetRes.pkt_pool", "NetRes.rxq.entries", "NetRes.rxq.waiters"],
        [1, 1, 1],
        1
    ),
    make_reservation(
        "parser",
        ["NetRes.stats"],
        [4],
        1
    )
]

val result = verify_reservations(leaves, tasks)

# All should pass:
# pkt_pool: 1*1=1 <= 8
# rxq.entries: 1*1=1 <= 8
# rxq.waiters: 1*1=1 <= 2
# stats: 4*1=4 <= 64
expect(result.has_errors).to_equal(false)
expect(result.total_checks).to_equal(4)
expect(result.passed_checks).to_equal(4)

# Verify individual demands
expect(result.demands[0].total_demand).to_equal(1)
expect(result.demands[1].total_demand).to_equal(1)
expect(result.demands[2].total_demand).to_equal(1)
expect(result.demands[3].total_demand).to_equal(4)

# Formatting should show pass
val output = format_reservation_result(result)
expect(output).to_contain("pass")
expect(output).to_contain("4/4 resources OK")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_reservation_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- get_task_reserve lookup
- Single resource demand
- Multi-resource checks
- Per-task breakdown
- Group-aware instances
- Zero reserves
- Edge cases
- Data structure construction
- Reservation formatting
- End-to-end: spec Section 11 NetRes scenario

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
