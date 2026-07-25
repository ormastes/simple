# Db Accel Planner Specification

> <details>

<!-- sdn-diagram:id=db_accel_planner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_accel_planner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_accel_planner_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_accel_planner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Accel Planner Specification

## Scenarios

### CostModel

#### cost_model_new sets row_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
expect(m.row_count).to_equal(1000)
```

</details>

#### cost_model_new defaults io_weight to 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(500)
expect(m.io_weight).to_equal(1.0)
```

</details>

#### cost_model_new defaults cpu_weight to 0.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(500)
expect(m.cpu_weight).to_equal(0.1)
```

</details>

#### cost_model_new defaults selectivity to 0.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(500)
expect(m.selectivity_default).to_equal(0.1)
```

</details>

#### cost_model_with_weights uses supplied weights

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_with_weights(100, 2.0, 0.5)
expect(m.io_weight).to_equal(2.0)
```

</details>

### PlanCost accessors

#### plan_cost_total returns total_cost field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PlanCost(estimated_rows: 10, io_cost: 5.0, cpu_cost: 1.0, total_cost: 6.0)
expect(plan_cost_total(c)).to_equal(6.0)
```

</details>

#### plan_cost_rows returns estimated_rows field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PlanCost(estimated_rows: 42, io_cost: 1.0, cpu_cost: 0.5, total_cost: 1.5)
expect(plan_cost_rows(c)).to_equal(42)
```

</details>

### estimate_cost

#### FullScan rows equals row_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
val pc = estimate_cost("FullScan", m)
expect(plan_cost_rows(pc)).to_equal(1000)
```

</details>

#### IndexLookup rows less than FullScan for large table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_rows(lookup) < plan_cost_rows(full)).to_equal(true)
```

</details>

#### IndexLookup total_cost less than FullScan total_cost for large table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_total(lookup) < plan_cost_total(full)).to_equal(true)
```

</details>

#### IndexRange rows less than FullScan for large table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val rng = estimate_cost("IndexRange", m)
expect(plan_cost_rows(rng) < plan_cost_rows(full)).to_equal(true)
```

</details>

#### IndexPrefix rows less than IndexRange for large table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1000)
val rng = estimate_cost("IndexRange", m)
val pfx = estimate_cost("IndexPrefix", m)
expect(plan_cost_rows(pfx) < plan_cost_rows(rng)).to_equal(true)
```

</details>

#### Join rows positive for any table

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(100)
val jn = estimate_cost("Join", m)
expect(plan_cost_rows(jn) > 0).to_equal(true)
```

</details>

#### unknown kind falls back to FullScan rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(200)
val unk = estimate_cost("Unknown", m)
val full = estimate_cost("FullScan", m)
expect(plan_cost_rows(unk)).to_equal(plan_cost_rows(full))
```

</details>

#### IndexLookup at min (1 row) returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = cost_model_new(1)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_rows(lookup)).to_equal(1)
```

</details>

### plan_query

#### Eq predicate with no indexes returns FullScan only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "val1")
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(1)
```

</details>

#### Eq predicate with matching BTree index returns two candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "val1")
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(2)
```

</details>

#### Range predicate with BTree index includes IndexRange candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_range("col_b", "a", "z")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len() >= 2).to_equal(true)
```

</details>

#### Prefix predicate with Prefix index includes IndexPrefix candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_prefix("col_c", "ns/")
val idx = index_descriptor_new("idx_c", "col_c", IndexKind.Prefix)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len() >= 2).to_equal(true)
```

</details>

#### Or predicate returns exactly one FullScan candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_a", "y")
val pred = predicate_or([p1, p2])
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(1)
```

</details>

#### And predicate with two children includes Join candidate

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_b", "y")
val pred = predicate_and([p1, p2])
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
# Two FullScans (one per child) + one Join
expect(candidates.len()).to_equal(3)
```

</details>

#### index on wrong column is not used for Eq predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "val1")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
# Only FullScan since index is on col_b, not col_a
expect(candidates.len()).to_equal(1)
```

</details>

### pick_best

#### empty candidates returns FullScan node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates: [PlanCandidate] = []
val nd = pick_best(candidates)
expect(nd.kind == PlanNodeKind.FullScan).to_equal(true)
```

</details>

#### single candidate is returned

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nd = plan_node_index_lookup("idx_x", "col_x")
val co = PlanCost(estimated_rows: 5, io_cost: 6.0, cpu_cost: 0.5, total_cost: 6.5)
val candidates = [PlanCandidate(node: nd, cost: co)]
val result = pick_best(candidates)
expect(result.kind == PlanNodeKind.IndexLookup).to_equal(true)
```

</details>

#### picks candidate with lower total_cost

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nd1 = plan_node_full_scan()
val co1 = PlanCost(estimated_rows: 1000, io_cost: 1000.0, cpu_cost: 100.0, total_cost: 1100.0)
val nd2 = plan_node_index_lookup("idx_x", "col_x")
val co2 = PlanCost(estimated_rows: 10, io_cost: 11.0, cpu_cost: 1.0, total_cost: 12.0)
val candidates = [PlanCandidate(node: nd1, cost: co1), PlanCandidate(node: nd2, cost: co2)]
val result = pick_best(candidates)
expect(result.kind == PlanNodeKind.IndexLookup).to_equal(true)
```

</details>

#### first wins on tie

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nd1 = plan_node_full_scan()
val co1 = PlanCost(estimated_rows: 100, io_cost: 50.0, cpu_cost: 5.0, total_cost: 55.0)
val nd2 = plan_node_index_lookup("idx_x", "col_x")
val co2 = PlanCost(estimated_rows: 100, io_cost: 50.0, cpu_cost: 5.0, total_cost: 55.0)
val candidates = [PlanCandidate(node: nd1, cost: co1), PlanCandidate(node: nd2, cost: co2)]
val result = pick_best(candidates)
expect(result.kind == PlanNodeKind.FullScan).to_equal(true)
```

</details>

### choose_plan

#### Eq with BTree index chooses IndexLookup over FullScan

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "42")
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind == PlanNodeKind.IndexLookup).to_equal(true)
```

</details>

#### Prefix with Prefix index chooses IndexPrefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_prefix("col_b", "ns/")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.Prefix)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind == PlanNodeKind.IndexPrefix).to_equal(true)
```

</details>

#### Range with BTree index chooses IndexRange

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_range("col_c", "a", "m")
val idx = index_descriptor_new("idx_c", "col_c", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind == PlanNodeKind.IndexRange).to_equal(true)
```

</details>

#### Eq with no indexes returns FullScan

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "x")
val indexes: [IndexDescriptor] = []
val nd = choose_plan(pred, indexes, 500)
expect(nd.kind == PlanNodeKind.FullScan).to_equal(true)
```

</details>

#### Or predicate always returns FullScan

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_a", "y")
val pred = predicate_or([p1, p2])
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.Hash)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 1000)
expect(nd.kind == PlanNodeKind.FullScan).to_equal(true)
```

</details>

#### index_name populated on IndexLookup result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_eq("col_a", "42")
val idx = index_descriptor_new("my_idx", "col_a", IndexKind.Hash)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.index_name).to_equal("my_idx")
```

</details>

#### predicate_column populated on IndexRange result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pred = predicate_range("col_d", "0", "9")
val idx = index_descriptor_new("idx_d", "col_d", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.predicate_column).to_equal("col_d")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CostModel
- PlanCost accessors
- estimate_cost
- plan_query
- pick_best
- choose_plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
