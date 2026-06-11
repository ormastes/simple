# Db Hardening Optimizer Specification

> 1. var t = db table new

<!-- sdn-diagram:id=db_hardening_optimizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_hardening_optimizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_hardening_optimizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_hardening_optimizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Hardening Optimizer Specification

## Scenarios

### DbTable index maintenance on insert

#### builds indexes after first insert

1. var t = db table new
2. t insert
   - Expected: prefix_index_size(ki) equals `1`
   - Expected: text_index_size(ti) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
t.insert("user:alice", "payload_a")
val ki = t.key_index()
val ti = t.text_idx()
expect(prefix_index_size(ki)).to_equal(1)
expect(text_index_size(ti)).to_equal(1)
```

</details>

#### indexes grow with each insert

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: prefix_index_size(ki) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("items")
t.insert("item:one", "v1")
t.insert("item:two", "v2")
t.insert("item:three", "v3")
val ki = t.key_index()
expect(prefix_index_size(ki)).to_equal(3)
```

</details>

#### marks indexes dirty after insert

1. var t = db table new
   - Expected: t.indexes_dirty() is false
2. t insert
   - Expected: t.indexes_dirty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
expect(t.indexes_dirty()).to_equal(false)
t.insert("k1", "v1")
expect(t.indexes_dirty()).to_equal(true)
```

</details>

### DbTable index maintenance on delete

#### removes entry from indexes after delete

1. var t = db table new
2. t insert
3. t insert
4. t delete by key
   - Expected: prefix_index_size(ki) equals `1`
   - Expected: hits.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
t.insert("user:alice", "a")
t.insert("user:bob", "b")
t.delete_by_key("user:alice")
val ki = t.key_index()
expect(prefix_index_size(ki)).to_equal(1)
val hits = prefix_index_lookup_exact(ki, "user:alice")
expect(hits.len()).to_equal(0)
```

</details>

#### still finds remaining entries after delete

1. var t = db table new
2. t insert
3. t insert
4. t delete by key
   - Expected: hits.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
t.insert("user:alice", "a")
t.insert("user:bob", "b")
t.delete_by_key("user:alice")
val ki = t.key_index()
val hits = prefix_index_lookup_exact(ki, "user:bob")
expect(hits.len()).to_equal(1)
```

</details>

### DbTable index maintenance on update

#### updates payload without changing index count

1. var t = db table new
2. t insert
3. t update
   - Expected: prefix_index_size(ki) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
t.insert("user:alice", "old_payload")
t.update("user:alice", "new_payload")
val ki = t.key_index()
expect(prefix_index_size(ki)).to_equal(1)
```

</details>

#### returns updated payload via get_by_id

1. var t = db table new
2. t update
   - Expected: payload equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
val id = t.insert("user:alice", "old")
t.update("user:alice", "new")
val payload = t.get_by_id(id)
expect(payload).to_equal("new")
```

</details>

#### returns false for non-existent key update

1. var t = db table new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("users")
val result = t.update("missing", "val")
expect(result).to_equal(false)
```

</details>

### cache invalidation after mutations

#### find_by_key returns not_found after delete

1. var t = db table new
2. t insert
3. t delete by key
   - Expected: id_after equals `row_not_found()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("k1", "v1")
val id_before = t.find_by_key("k1")
expect(id_before).to_be_greater_than(-1)
t.delete_by_key("k1")
val id_after = t.find_by_key("k1")
expect(id_after).to_equal(row_not_found())
```

</details>

#### prefix scan reflects inserts immediately

1. var t = db table new
2. t insert
   - Expected: qr1.count equals `1`
3. t insert
   - Expected: qr2.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("log")
t.insert("log:a", "1")
val qr1 = db_table_prefix_scan(t, "log:")
expect(qr1.count).to_equal(1)
t.insert("log:b", "2")
val qr2 = db_table_prefix_scan(t, "log:")
expect(qr2.count).to_equal(2)
```

</details>

#### exact match reflects delete

1. var t = db table new
2. t insert
3. t insert
   - Expected: qr1.count equals `1`
4. t delete by key
   - Expected: qr2.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("key1", "v1")
t.insert("key2", "v2")
val qr1 = db_table_exact_match(t, "key1")
expect(qr1.count).to_equal(1)
t.delete_by_key("key1")
val qr2 = db_table_exact_match(t, "key1")
expect(qr2.count).to_equal(0)
```

</details>

#### contains scan reflects update

1. var t = db table new
2. t insert
   - Expected: qr1.count equals `1`
3. t delete by key
4. t insert
   - Expected: qr2.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("user:alice", "admin")
val qr1 = db_table_contains_scan(t, "alice")
expect(qr1.count).to_equal(1)
t.delete_by_key("user:alice")
t.insert("user:bob", "viewer")
val qr2 = db_table_contains_scan(t, "alice")
expect(qr2.count).to_equal(0)
```

</details>

### planner-driven indexed queries

#### db_table_prefix_scan uses index for prefix

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("data")
t.insert("ns:a", "1")
t.insert("ns:b", "2")
t.insert("other:c", "3")
val qr = db_table_prefix_scan(t, "ns:")
expect(qr.count).to_equal(2)
```

</details>

#### db_table_exact_match uses index for exact

1. var t = db table new
2. t insert
3. t insert
   - Expected: qr.count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("data")
t.insert("key:one", "1")
t.insert("key:two", "2")
val qr = db_table_exact_match(t, "key:one")
expect(qr.count).to_equal(1)
```

</details>

#### db_table_contains_scan uses text index

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("data")
t.insert("hello_world", "1")
t.insert("hello_there", "2")
t.insert("goodbye", "3")
val qr = db_table_contains_scan(t, "hello")
expect(qr.count).to_equal(2)
```

</details>

#### db_table_range_scan works on ids

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("data")
t.insert("a", "1")
t.insert("b", "2")
t.insert("c", "3")
val qr = db_table_range_scan(t, 0, 1)
expect(qr.count).to_equal(2)
```

</details>

#### db_table_all_ids returns all

1. var t = db table new
2. t insert
3. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("data")
t.insert("a", "1")
t.insert("b", "2")
val qr = db_table_all_ids(t)
expect(qr.count).to_equal(2)
```

</details>

### legacy raw-row query backward compat

#### db_prefix_scan still works on raw rows

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("log")
t.insert("log:x", "1")
t.insert("log:y", "2")
t.insert("other:z", "3")
val qr = db_prefix_scan(t.rows, "log:")
expect(qr.count).to_equal(2)
```

</details>

#### db_keys_matching still works on raw rows

1. var t = db table new
2. t insert
3. t insert
   - Expected: qr.count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("k1", "v1")
t.insert("k2", "v2")
val qr = db_keys_matching(t.rows, "k1")
expect(qr.count).to_equal(1)
```

</details>

#### db_range_scan still works on raw rows

1. var t = db table new
2. t insert
3. t insert
4. t insert
   - Expected: qr.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("a", "1")
t.insert("b", "2")
t.insert("c", "3")
val qr = db_range_scan(t.rows, 0, 1)
expect(qr.count).to_equal(2)
```

</details>

#### db_all_ids still works on raw rows

1. var t = db table new
2. t insert
   - Expected: qr.count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("test")
t.insert("a", "1")
val qr = db_all_ids(t.rows)
expect(qr.count).to_equal(1)
```

</details>

### empty table queries

#### prefix scan on empty table returns 0

1. var t = db table new
   - Expected: qr.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("empty")
val qr = db_table_prefix_scan(t, "any:")
expect(qr.count).to_equal(0)
```

</details>

#### exact match on empty table returns 0

1. var t = db table new
   - Expected: qr.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("empty")
val qr = db_table_exact_match(t, "any")
expect(qr.count).to_equal(0)
```

</details>

#### contains scan on empty table returns 0

1. var t = db table new
   - Expected: qr.count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("empty")
val qr = db_table_contains_scan(t, "x")
expect(qr.count).to_equal(0)
```

</details>

#### has_indexes returns false on empty table

1. var t = db table new
   - Expected: t.has_indexes() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = db_table_new("empty")
expect(t.has_indexes()).to_equal(false)
```

</details>

### direct planner plan selection

#### choose_plan selects IndexPrefix with prefix index available

1. descs push
   - Expected: plan.kind equals `PlanNodeKind.IndexPrefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var descs: [IndexDescriptor] = []
descs.push(index_descriptor_new("key_prefix", "key", IndexKind.Prefix))
val pred = predicate_prefix("key", "ns:")
val plan = choose_plan(pred, descs, 100)
expect(plan.kind).to_equal(PlanNodeKind.IndexPrefix)
```

</details>

#### choose_plan falls back to FullScan with no indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var descs: [IndexDescriptor] = []
val pred = predicate_prefix("key", "ns:")
val plan = choose_plan(pred, descs, 100)
expect(plan.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

#### choose_plan selects IndexLookup for eq with hash index

1. descs push
   - Expected: plan.kind equals `PlanNodeKind.IndexLookup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var descs: [IndexDescriptor] = []
descs.push(index_descriptor_new("key_hash", "key", IndexKind.Hash))
val pred = predicate_eq("key", "user:alice")
val plan = choose_plan(pred, descs, 100)
expect(plan.kind).to_equal(PlanNodeKind.IndexLookup)
```

</details>

#### choose_plan falls back to FullScan for eq with no indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var descs: [IndexDescriptor] = []
val pred = predicate_eq("key", "user:alice")
val plan = choose_plan(pred, descs, 100)
expect(plan.kind).to_equal(PlanNodeKind.FullScan)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/db_hardening_optimizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DbTable index maintenance on insert
- DbTable index maintenance on delete
- DbTable index maintenance on update
- cache invalidation after mutations
- planner-driven indexed queries
- legacy raw-row query backward compat
- empty table queries
- direct planner plan selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
