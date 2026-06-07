# Cardinality Estimator Specification

> <details>

<!-- sdn-diagram:id=cardinality_estimator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cardinality_estimator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cardinality_estimator_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cardinality_estimator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cardinality Estimator Specification

## Scenarios

### DB learned cardinality estimator

#### is disabled unless explicitly opted in

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val estimator = learned_cardinality_new(false)
val estimate = learned_cardinality_estimate(estimator, "prefix:key:user", 1000, 100, 12)

expect(estimate.source).to_equal("disabled")
expect(estimate.estimated_rows).to_equal(100)
expect(estimate.observation_count).to_equal(0)
```

</details>

#### coexists with BRIN and conventional estimates before learning

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val estimator = learned_cardinality_new(true)
val brin_estimate = learned_cardinality_estimate(estimator, "range:id:10..20", 1000, 200, 32)
val conventional_estimate = learned_cardinality_estimate(estimator, "prefix:key:admin", 1000, 50, -1)

expect(brin_estimate.source).to_equal("brin")
expect(brin_estimate.estimated_rows).to_equal(32)
expect(conventional_estimate.source).to_equal("conventional")
expect(conventional_estimate.estimated_rows).to_equal(50)
```

</details>

#### records estimation error against exact scan counts and learns later estimates

1. var estimator = learned cardinality new
2. estimator = learned cardinality record
   - Expected: learned_cardinality_observation_count(estimator) equals `1`
   - Expected: learned.source equals `learned`
   - Expected: learned.estimated_rows equals `24`
   - Expected: learned.observation_count equals `1`
   - Expected: learned.abs_error equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var estimator = learned_cardinality_new(true)
val first = learned_cardinality_estimate(estimator, "prefix:key:user", 1000, 100, -1)
estimator = learned_cardinality_record(estimator, first, 24)
val learned = learned_cardinality_estimate(estimator, "prefix:key:user", 1000, 100, -1)

expect(learned_cardinality_observation_count(estimator)).to_equal(1)
expect(learned.source).to_equal("learned")
expect(learned.estimated_rows).to_equal(24)
expect(learned.observation_count).to_equal(1)
expect(learned.abs_error).to_equal(76)
```

</details>

#### does not alter query execution correctness when disabled

1. table insert
2. table insert
3. table insert
   - Expected: estimate.source equals `disabled`
   - Expected: before.count equals `2`
   - Expected: after.count equals `2`
   - Expected: before.ids[0] equals `after.ids[0]`
   - Expected: before.ids[1] equals `after.ids[1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = db_table_new("users")
table.insert("user/alice", "a")
table.insert("user/bob", "b")
table.insert("admin/root", "r")
val before = db_table_prefix_scan(table, "user/")
val estimator = learned_cardinality_new(false)
val estimate = learned_cardinality_estimate(estimator, "prefix:key:user/", table.row_count(), 1, -1)
val after = db_table_prefix_scan(table, "user/")

expect(estimate.source).to_equal("disabled")
expect(before.count).to_equal(2)
expect(after.count).to_equal(2)
expect(before.ids[0]).to_equal(after.ids[0])
expect(before.ids[1]).to_equal(after.ids[1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/cardinality_estimator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DB learned cardinality estimator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
