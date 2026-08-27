# db_accel_planner_spec

> Purpose: cost_model_new sets row_count

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# db_accel_planner_spec

Purpose: cost_model_new sets row_count

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: cost_model_new sets row_count
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### CostModel

#### cost_model_new sets row_count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cost_model_new sets row_count
- Verify: cost_model_new sets row_count
   - Expected: m.row_count equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cost_model_new sets row_count")
step("Verify: cost_model_new sets row_count")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
expect(m.row_count).to_equal(1000)  # oracle: value fixed by the spec contract
```

</details>

#### cost_model_new defaults io_weight to 1.0

- cost_model_new defaults io_weight to 1.0
- Verify: cost_model_new defaults io_weight to 1.0
   - Expected: m.io_weight equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cost_model_new defaults io_weight to 1.0")
step("Verify: cost_model_new defaults io_weight to 1.0")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(500)
expect(m.io_weight).to_equal(1.0)
```

</details>

#### cost_model_new defaults cpu_weight to 0.1

- cost_model_new defaults cpu_weight to 0.1
- Verify: cost_model_new defaults cpu_weight to 0.1
   - Expected: m.cpu_weight equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cost_model_new defaults cpu_weight to 0.1")
step("Verify: cost_model_new defaults cpu_weight to 0.1")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(500)
expect(m.cpu_weight).to_equal(0.1)
```

</details>

#### cost_model_new defaults selectivity to 0.1

- cost_model_new defaults selectivity to 0.1
- Verify: cost_model_new defaults selectivity to 0.1
   - Expected: m.selectivity_default equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cost_model_new defaults selectivity to 0.1")
step("Verify: cost_model_new defaults selectivity to 0.1")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(500)
expect(m.selectivity_default).to_equal(0.1)
```

</details>

#### cost_model_with_weights uses supplied weights

- cost_model_with_weights uses supplied weights
- Verify: cost_model_with_weights uses supplied weights
   - Expected: m.io_weight equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cost_model_with_weights uses supplied weights")
step("Verify: cost_model_with_weights uses supplied weights")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_with_weights(100, 2.0, 0.5)
expect(m.io_weight).to_equal(2.0)
```

</details>

### PlanCost accessors

#### plan_cost_total returns total_cost field

- plan_cost_total returns total_cost field
- Verify: plan_cost_total returns total_cost field
   - Expected: plan_cost_total(c) equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("plan_cost_total returns total_cost field")
step("Verify: plan_cost_total returns total_cost field")
# @req: REQ-BENCH-DbAccePlan-001
val c = PlanCost(estimated_rows: 10, io_cost: 5.0, cpu_cost: 1.0, total_cost: 6.0)
expect(plan_cost_total(c)).to_equal(6.0)
```

</details>

#### plan_cost_rows returns estimated_rows field

- plan_cost_rows returns estimated_rows field
- Verify: plan_cost_rows returns estimated_rows field
   - Expected: plan_cost_rows(c) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("plan_cost_rows returns estimated_rows field")
step("Verify: plan_cost_rows returns estimated_rows field")
# @req: REQ-BENCH-DbAccePlan-001
val c = PlanCost(estimated_rows: 42, io_cost: 1.0, cpu_cost: 0.5, total_cost: 1.5)
expect(plan_cost_rows(c)).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

### estimate_cost

#### FullScan rows equals row_count

- FullScan rows equals row_count
- Verify: FullScan rows equals row_count
   - Expected: plan_cost_rows(pc) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("FullScan rows equals row_count")
step("Verify: FullScan rows equals row_count")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
val pc = estimate_cost("FullScan", m)
expect(plan_cost_rows(pc)).to_equal(1000)  # oracle: value fixed by the spec contract
```

</details>

#### IndexLookup rows less than FullScan for large table

- IndexLookup rows less than FullScan for large table
- Verify: IndexLookup rows less than FullScan for large table
   - Expected: plan_cost_rows(lookup) < plan_cost_rows(full) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("IndexLookup rows less than FullScan for large table")
step("Verify: IndexLookup rows less than FullScan for large table")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_rows(lookup) < plan_cost_rows(full)).to_equal(true)
```

</details>

#### IndexLookup total_cost less than FullScan total_cost for large table

- IndexLookup total_cost less than FullScan total_cost for large table
- Verify: IndexLookup total_cost less than FullScan total_cost for large table
   - Expected: plan_cost_total(lookup) < plan_cost_total(full) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("IndexLookup total_cost less than FullScan total_cost for large table")
step("Verify: IndexLookup total_cost less than FullScan total_cost for large table")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_total(lookup) < plan_cost_total(full)).to_equal(true)
```

</details>

#### IndexRange rows less than FullScan for large table

- IndexRange rows less than FullScan for large table
- Verify: IndexRange rows less than FullScan for large table
   - Expected: plan_cost_rows(rng) < plan_cost_rows(full) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("IndexRange rows less than FullScan for large table")
step("Verify: IndexRange rows less than FullScan for large table")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
val full = estimate_cost("FullScan", m)
val rng = estimate_cost("IndexRange", m)
expect(plan_cost_rows(rng) < plan_cost_rows(full)).to_equal(true)
```

</details>

#### IndexPrefix rows less than IndexRange for large table

- IndexPrefix rows less than IndexRange for large table
- Verify: IndexPrefix rows less than IndexRange for large table
   - Expected: plan_cost_rows(pfx) < plan_cost_rows(rng) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("IndexPrefix rows less than IndexRange for large table")
step("Verify: IndexPrefix rows less than IndexRange for large table")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1000)
val rng = estimate_cost("IndexRange", m)
val pfx = estimate_cost("IndexPrefix", m)
expect(plan_cost_rows(pfx) < plan_cost_rows(rng)).to_equal(true)
```

</details>

#### Join rows positive for any table

- Join rows positive for any table
- Verify: Join rows positive for any table
   - Expected: plan_cost_rows(jn) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Join rows positive for any table")
step("Verify: Join rows positive for any table")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(100)
val jn = estimate_cost("Join", m)
expect(plan_cost_rows(jn) > 0).to_equal(true)
```

</details>

#### unknown kind falls back to FullScan rows

- unknown kind falls back to FullScan rows
- Verify: unknown kind falls back to FullScan rows
   - Expected: plan_cost_rows(unk) equals `plan_cost_rows(full)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("unknown kind falls back to FullScan rows")
step("Verify: unknown kind falls back to FullScan rows")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(200)
val unk = estimate_cost("Unknown", m)
val full = estimate_cost("FullScan", m)
expect(plan_cost_rows(unk)).to_equal(plan_cost_rows(full))
```

</details>

#### IndexLookup at min (1 row) returns 1

- IndexLookup at min (1 row) returns 1
- Verify: IndexLookup at min (1 row) returns 1
   - Expected: plan_cost_rows(lookup) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("IndexLookup at min (1 row) returns 1")
step("Verify: IndexLookup at min (1 row) returns 1")
# @req: REQ-BENCH-DbAccePlan-001
val m = cost_model_new(1)
val lookup = estimate_cost("IndexLookup", m)
expect(plan_cost_rows(lookup)).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

### plan_query

#### Eq predicate with no indexes returns FullScan only

- Eq predicate with no indexes returns FullScan only
- Verify: Eq predicate with no indexes returns FullScan only
   - Expected: candidates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Eq predicate with no indexes returns FullScan only")
step("Verify: Eq predicate with no indexes returns FullScan only")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "val1")
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### Eq predicate with matching BTree index returns two candidates

- Eq predicate with matching BTree index returns two candidates
- Verify: Eq predicate with matching BTree index returns two candidates
   - Expected: candidates.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Eq predicate with matching BTree index returns two candidates")
step("Verify: Eq predicate with matching BTree index returns two candidates")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "val1")
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### Range predicate with BTree index includes IndexRange candidate

- Range predicate with BTree index includes IndexRange candidate
- Verify: Range predicate with BTree index includes IndexRange candidate
   - Expected: candidates.len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Range predicate with BTree index includes IndexRange candidate")
step("Verify: Range predicate with BTree index includes IndexRange candidate")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_range("col_b", "a", "z")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len() >= 2).to_equal(true)
```

</details>

#### Prefix predicate with Prefix index includes IndexPrefix candidate

- Prefix predicate with Prefix index includes IndexPrefix candidate
- Verify: Prefix predicate with Prefix index includes IndexPrefix candidate
   - Expected: candidates.len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Prefix predicate with Prefix index includes IndexPrefix candidate")
step("Verify: Prefix predicate with Prefix index includes IndexPrefix candidate")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_prefix("col_c", "ns/")
val idx = index_descriptor_new("idx_c", "col_c", IndexKind.Prefix)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len() >= 2).to_equal(true)
```

</details>

#### Or predicate returns exactly one FullScan candidate

- Or predicate returns exactly one FullScan candidate
- Verify: Or predicate returns exactly one FullScan candidate
   - Expected: candidates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Or predicate returns exactly one FullScan candidate")
step("Verify: Or predicate returns exactly one FullScan candidate")
# @req: REQ-BENCH-DbAccePlan-001
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_a", "y")
val pred = predicate_or([p1, p2])
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
expect(candidates.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### And predicate with two children includes Join candidate

- And predicate with two children includes Join candidate
- Verify: And predicate with two children includes Join candidate
   - Expected: candidates.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("And predicate with two children includes Join candidate")
step("Verify: And predicate with two children includes Join candidate")
# @req: REQ-BENCH-DbAccePlan-001
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_b", "y")
val pred = predicate_and([p1, p2])
val indexes: [IndexDescriptor] = []
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
# Two FullScans (one per child) + one Join
expect(candidates.len()).to_equal(3)  # oracle: value fixed by the spec contract
```

</details>

#### index on wrong column is not used for Eq predicate

- index on wrong column is not used for Eq predicate
- Verify: index on wrong column is not used for Eq predicate
   - Expected: candidates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("index on wrong column is not used for Eq predicate")
step("Verify: index on wrong column is not used for Eq predicate")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "val1")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.BTree)
val indexes = [idx]
val m = cost_model_new(500)
val candidates = plan_query(pred, indexes, m)
# Only FullScan since index is on col_b, not col_a
expect(candidates.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

### pick_best

#### empty candidates returns FullScan node

- empty candidates returns FullScan node
- Verify: empty candidates returns FullScan node
   - Expected: nd.kind equals `PlanNodeKind.FullScan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("empty candidates returns FullScan node")
step("Verify: empty candidates returns FullScan node")
# @req: REQ-BENCH-DbAccePlan-001
val candidates: [PlanCandidate] = []
val nd = pick_best(candidates)
expect(nd.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

#### single candidate is returned

- single candidate is returned
- Verify: single candidate is returned
   - Expected: result.kind equals `PlanNodeKind.IndexLookup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("single candidate is returned")
step("Verify: single candidate is returned")
# @req: REQ-BENCH-DbAccePlan-001
val nd = plan_node_index_lookup("idx_x", "col_x")
val co = PlanCost(estimated_rows: 5, io_cost: 6.0, cpu_cost: 0.5, total_cost: 6.5)
val candidates = [PlanCandidate(node: nd, cost: co)]
val result = pick_best(candidates)
expect(result.kind).to_equal(PlanNodeKind.IndexLookup)
```

</details>

#### picks candidate with lower total_cost

- picks candidate with lower total_cost
- Verify: picks candidate with lower total_cost
   - Expected: result.kind equals `PlanNodeKind.IndexLookup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("picks candidate with lower total_cost")
step("Verify: picks candidate with lower total_cost")
# @req: REQ-BENCH-DbAccePlan-001
val nd1 = plan_node_full_scan()
val co1 = PlanCost(estimated_rows: 1000, io_cost: 1000.0, cpu_cost: 100.0, total_cost: 1100.0)
val nd2 = plan_node_index_lookup("idx_x", "col_x")
val co2 = PlanCost(estimated_rows: 10, io_cost: 11.0, cpu_cost: 1.0, total_cost: 12.0)
val candidates = [PlanCandidate(node: nd1, cost: co1), PlanCandidate(node: nd2, cost: co2)]
val result = pick_best(candidates)
expect(result.kind).to_equal(PlanNodeKind.IndexLookup)
```

</details>

#### first wins on tie

- first wins on tie
- Verify: first wins on tie
   - Expected: result.kind equals `PlanNodeKind.FullScan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("first wins on tie")
step("Verify: first wins on tie")
# @req: REQ-BENCH-DbAccePlan-001
val nd1 = plan_node_full_scan()
val co1 = PlanCost(estimated_rows: 100, io_cost: 50.0, cpu_cost: 5.0, total_cost: 55.0)
val nd2 = plan_node_index_lookup("idx_x", "col_x")
val co2 = PlanCost(estimated_rows: 100, io_cost: 50.0, cpu_cost: 5.0, total_cost: 55.0)
val candidates = [PlanCandidate(node: nd1, cost: co1), PlanCandidate(node: nd2, cost: co2)]
val result = pick_best(candidates)
expect(result.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

### choose_plan

#### Eq with BTree index chooses IndexLookup over FullScan

- Eq with BTree index chooses IndexLookup over FullScan
- Verify: Eq with BTree index chooses IndexLookup over FullScan
   - Expected: nd.kind equals `PlanNodeKind.IndexLookup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Eq with BTree index chooses IndexLookup over FullScan")
step("Verify: Eq with BTree index chooses IndexLookup over FullScan")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "42")
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind).to_equal(PlanNodeKind.IndexLookup)
```

</details>

#### Prefix with Prefix index chooses IndexPrefix

- Prefix with Prefix index chooses IndexPrefix
- Verify: Prefix with Prefix index chooses IndexPrefix
   - Expected: nd.kind equals `PlanNodeKind.IndexPrefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Prefix with Prefix index chooses IndexPrefix")
step("Verify: Prefix with Prefix index chooses IndexPrefix")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_prefix("col_b", "ns/")
val idx = index_descriptor_new("idx_b", "col_b", IndexKind.Prefix)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind).to_equal(PlanNodeKind.IndexPrefix)
```

</details>

#### Range with BTree index chooses IndexRange

- Range with BTree index chooses IndexRange
- Verify: Range with BTree index chooses IndexRange
   - Expected: nd.kind equals `PlanNodeKind.IndexRange`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Range with BTree index chooses IndexRange")
step("Verify: Range with BTree index chooses IndexRange")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_range("col_c", "a", "m")
val idx = index_descriptor_new("idx_c", "col_c", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.kind).to_equal(PlanNodeKind.IndexRange)
```

</details>

#### Eq with no indexes returns FullScan

- Eq with no indexes returns FullScan
- Verify: Eq with no indexes returns FullScan
   - Expected: nd.kind equals `PlanNodeKind.FullScan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Eq with no indexes returns FullScan")
step("Verify: Eq with no indexes returns FullScan")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "x")
val indexes: [IndexDescriptor] = []
val nd = choose_plan(pred, indexes, 500)
expect(nd.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

#### Or predicate always returns FullScan

- Or predicate always returns FullScan
- Verify: Or predicate always returns FullScan
   - Expected: nd.kind equals `PlanNodeKind.FullScan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("Or predicate always returns FullScan")
step("Verify: Or predicate always returns FullScan")
# @req: REQ-BENCH-DbAccePlan-001
val p1 = predicate_eq("col_a", "x")
val p2 = predicate_eq("col_a", "y")
val pred = predicate_or([p1, p2])
val idx = index_descriptor_new("idx_a", "col_a", IndexKind.Hash)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 1000)
expect(nd.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

#### index_name populated on IndexLookup result

- index_name populated on IndexLookup result
- Verify: index_name populated on IndexLookup result
   - Expected: nd.index_name equals `my_idx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("index_name populated on IndexLookup result")
step("Verify: index_name populated on IndexLookup result")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_eq("col_a", "42")
val idx = index_descriptor_new("my_idx", "col_a", IndexKind.Hash)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.index_name).to_equal("my_idx")
```

</details>

#### predicate_column populated on IndexRange result

- predicate_column populated on IndexRange result
- Verify: predicate_column populated on IndexRange result
   - Expected: nd.predicate_column equals `col_d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("predicate_column populated on IndexRange result")
step("Verify: predicate_column populated on IndexRange result")
# @req: REQ-BENCH-DbAccePlan-001
val pred = predicate_range("col_d", "0", "9")
val idx = index_descriptor_new("idx_d", "col_d", IndexKind.BTree)
val indexes = [idx]
val nd = choose_plan(pred, indexes, 10000)
expect(nd.predicate_column).to_equal("col_d")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
- `REQ-BENCH-DbAccePlan-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d73caa7f64c3d35419c6f7842178878b5a18265b12a3a7e726a1875a8c2c85f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d73caa7f64c3d35419c6f7842178878b5a18265b12a3a7e726a1875a8c2c85f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d73caa7f64c3d35419c6f7842178878b5a18265b12a3a7e726a1875a8c2c85f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl
mirror: doc/06_spec/05_perf/bench/db_accel_planner/db_accel_planner_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/bench/db_accel_planner/db_accel_planner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/bench/db_accel_planner/db_accel_planner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl:409:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cost_model_new sets row_count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl:417:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cost_model_new defaults io_weight to 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/bench/db_accel_planner/db_accel_planner_spec.spl:425:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cost_model_new defaults cpu_weight to 0.1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
