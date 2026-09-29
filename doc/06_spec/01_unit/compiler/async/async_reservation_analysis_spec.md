# async_reservation_analysis_spec

> Purpose: Prove that get_task_reserve lookup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_reservation_analysis_spec

Purpose: Prove that get_task_reserve lookup.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_reservation_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that get_task_reserve lookup.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### get_task_reserve lookup

#### returns count for existing path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns count for existing path
- Verify: returns count for existing path
   - Expected: get_task_reserve(task, "NetRes.pkt_pool") equals `2`
   - Expected: get_task_reserve(task, "NetRes.rxq.entries") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns count for existing path")
step("Verify: returns count for existing path")
# @req: REQ-COMP-GET-TASK-RESERVE-LOOKUP-001
val task = make_reservation("uart_rx", ["NetRes.pkt_pool", "NetRes.rxq.entries"], [2, 1], 1)
expect(get_task_reserve(task, "NetRes.pkt_pool")).to_equal(2)
expect(get_task_reserve(task, "NetRes.rxq.entries")).to_equal(1)
```

</details>

#### returns zero for missing path

- returns zero for missing path
- Verify: returns zero for missing path
   - Expected: get_task_reserve(task, "NetRes.stats") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns zero for missing path")
step("Verify: returns zero for missing path")
val task = make_reservation("uart_rx", ["NetRes.pkt_pool"], [2], 1)
expect(get_task_reserve(task, "NetRes.stats")).to_equal(0)
```

</details>

#### returns zero for empty reserves

- returns zero for empty reserves
- Verify: returns zero for empty reserves
   - Expected: get_task_reserve(task, "NetRes.pkt_pool") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns zero for empty reserves")
step("Verify: returns zero for empty reserves")
val task = make_empty_reservation("idle_task", 1)
expect(get_task_reserve(task, "NetRes.pkt_pool")).to_equal(0)
```

</details>

### Single resource demand

#### passes when demand within capacity

- passes when demand within capacity
- Verify: passes when demand within capacity
   - Expected: result.has_errors is false
   - Expected: result.passed_checks equals `1`
   - Expected: result.total_checks equals `1`
   - Expected: result.demands[0].total_demand equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when demand within capacity")
step("Verify: passes when demand within capacity")
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

- passes when demand equals capacity
- Verify: passes when demand equals capacity
   - Expected: result.has_errors is false
   - Expected: result.demands[0].total_demand equals `8`
   - Expected: result.demands[0].overflow is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when demand equals capacity")
step("Verify: passes when demand equals capacity")
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

- errors when demand exceeds capacity
- Verify: errors when demand exceeds capacity
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands[0].total_demand equals `7`
   - Expected: result.demands[0].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when demand exceeds capacity")
step("Verify: errors when demand exceeds capacity")
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

- passes when all resources within capacity
- Verify: passes when all resources within capacity
   - Expected: result.has_errors is false
   - Expected: result.passed_checks equals `2`
   - Expected: result.total_checks equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when all resources within capacity")
step("Verify: passes when all resources within capacity")
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

- errors when one resource overflows
- Verify: errors when one resource overflows
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `1`
   - Expected: result.demands[0].overflow is false
   - Expected: result.demands[1].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when one resource overflows")
step("Verify: errors when one resource overflows")
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

- errors when all resources overflow
- Verify: errors when all resources overflow
   - Expected: result.has_errors is true
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands[0].overflow is true
   - Expected: result.demands[1].overflow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when all resources overflow")
step("Verify: errors when all resources overflow")
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

- tracks contributor names
- Verify: tracks contributor names
   - Expected: demand.contributor_names.len() equals `2`
   - Expected: demand.contributor_names[0] equals `uart_rx`
   - Expected: demand.contributor_names[1] equals `parser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks contributor names")
step("Verify: tracks contributor names")
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

- tracks contributor amounts
- Verify: tracks contributor amounts
   - Expected: demand.contributor_amounts[0] equals `6`
   - Expected: demand.contributor_amounts[1] equals `8`
   - Expected: demand.total_demand equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tracks contributor amounts")
step("Verify: tracks contributor amounts")
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

- uses exact spawn counts not declared instances
- Verify: uses exact spawn counts not declared instances
   - Expected: result.has_errors is false
   - Expected: result.demands[0].total_demand equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses exact spawn counts not declared instances")
step("Verify: uses exact spawn counts not declared instances")
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

- would overflow with declared instances but not with actual
- Verify: would overflow with declared instances but not with actual
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("would overflow with declared instances but not with actual")
step("Verify: would overflow with declared instances but not with actual")
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

- task with no reserves contributes nothing
- Verify: task with no reserves contributes nothing
   - Expected: result.demands[0].total_demand equals `2`
   - Expected: result.demands[0].contributor_names.len() equals `1`
   - Expected: result.demands[0].contributor_names[0] equals `worker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("task with no reserves contributes nothing")
step("Verify: task with no reserves contributes nothing")
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

- resource with no reservers has zero demand
- Verify: resource with no reservers has zero demand
   - Expected: result.demands[0].total_demand equals `0`
   - Expected: result.demands[0].overflow is false
   - Expected: result.demands[0].contributor_names.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resource with no reservers has zero demand")
step("Verify: resource with no reservers has zero demand")
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

- handles empty leaves list
- Verify: handles empty leaves list
   - Expected: result.has_errors is false
   - Expected: result.total_checks equals `0`
   - Expected: result.passed_checks equals `0`
   - Expected: result.demands.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles empty leaves list")
step("Verify: handles empty leaves list")
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

- handles empty tasks list
- Verify: handles empty tasks list
   - Expected: result.has_errors is false
   - Expected: result.total_checks equals `1`
   - Expected: result.passed_checks equals `1`
   - Expected: result.demands[0].total_demand equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles empty tasks list")
step("Verify: handles empty tasks list")
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

- creates ResourceLeaf correctly
- Verify: creates ResourceLeaf correctly
   - Expected: leaf.path equals `NetRes.pkt_pool`
   - Expected: leaf.unit_name equals `PktBuf`
   - Expected: leaf.cap equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates ResourceLeaf correctly")
step("Verify: creates ResourceLeaf correctly")
val leaf = make_leaf("NetRes.pkt_pool", "PktBuf", 8)
expect(leaf.path).to_equal("NetRes.pkt_pool")
expect(leaf.unit_name).to_equal("PktBuf")
expect(leaf.cap).to_equal(8)
```

</details>

#### creates TaskReservation correctly

- creates TaskReservation correctly
- Verify: creates TaskReservation correctly
   - Expected: task.task_name equals `uart_rx`
   - Expected: task.reserve_paths.len() equals `2`
   - Expected: task.reserve_counts.len() equals `2`
   - Expected: task.instances equals `4`
   - Expected: task.reserve_paths[0] equals `pool_a`
   - Expected: task.reserve_counts[1] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates TaskReservation correctly")
step("Verify: creates TaskReservation correctly")
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

- creates ReservationDemand via compute_demand
- Verify: creates ReservationDemand via compute_demand
   - Expected: demand.resource_path equals `pool`
   - Expected: demand.total_demand equals `6`
   - Expected: demand.cap equals `10`
   - Expected: demand.overflow is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates ReservationDemand via compute_demand")
step("Verify: creates ReservationDemand via compute_demand")
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

- formats passing result
- Verify: formats passing result


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats passing result")
step("Verify: formats passing result")
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

- formats failing result with overflow details
- Verify: formats failing result with overflow details


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats failing result with overflow details")
step("Verify: formats failing result with overflow details")
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

- validates full NetRes resource set
- Verify: validates full NetRes resource set
   - Expected: result.has_errors is false
   - Expected: result.total_checks equals `4`
   - Expected: result.passed_checks equals `4`
   - Expected: result.demands[0].total_demand equals `1`
   - Expected: result.demands[1].total_demand equals `1`
   - Expected: result.demands[2].total_demand equals `1`
   - Expected: result.demands[3].total_demand equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates full NetRes resource set")
step("Verify: validates full NetRes resource set")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-GET-TASK-RESERVE-LOOKUP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcf5a8bba5a018f33e9b800a3646038173cb3fdf5a83fa664f95847f61e5aa23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcf5a8bba5a018f33e9b800a3646038173cb3fdf5a83fa664f95847f61e5aa23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcf5a8bba5a018f33e9b800a3646038173cb3fdf5a83fa664f95847f61e5aa23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/async/async_reservation_analysis_spec.spl
mirror: doc/06_spec/01_unit/compiler/async/async_reservation_analysis_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/async/async_reservation_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/async/async_reservation_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/async/async_reservation_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/async/async_reservation_analysis_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns count for existing path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_reservation_analysis_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for missing path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_reservation_analysis_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for empty reserves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
