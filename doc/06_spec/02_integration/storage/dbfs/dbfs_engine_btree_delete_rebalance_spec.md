# BTree Delete Rebalancing Specification

> Tests the CLRS top-down proactive fix-up for BTree deletion:

<!-- sdn-diagram:id=dbfs_engine_btree_delete_rebalance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_btree_delete_rebalance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_btree_delete_rebalance_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_btree_delete_rebalance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BTree Delete Rebalancing Specification

Tests the CLRS top-down proactive fix-up for BTree deletion:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no implementation yet) |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests the CLRS top-down proactive fix-up for BTree deletion:
ensure_min_keys, borrow_from_left, borrow_from_right, merge_children.
Without rebalancing, deletions can leave underflowed nodes that violate
the BTree invariant (each non-root node has >= t keys).

BTree<V> uses BTreeKey { a: i64, b: i64 } as composite key with
lexicographic ordering. We use b=0 for simple single-dimension keys.

## Scenarios

### BTree delete

### leaf deletion

#### removes a key from a single-node tree

1. var tree = make tree
2. delete key
   - Expected: has(tree, 20) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30])
delete_key(tree, 20)
expect(has(tree, 20)).to_equal(false)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
```

</details>

#### removes all keys leaving empty tree

1. var tree = make tree
2. delete key
3. delete key
   - Expected: has(tree, 5) is false
   - Expected: has(tree, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([5, 10])
delete_key(tree, 5)
delete_key(tree, 10)
expect(has(tree, 5)).to_equal(false)
expect(has(tree, 10)).to_equal(false)
```

</details>

#### delete of nonexistent key is a no-op

1. var tree = make tree
2. delete key
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30])
delete_key(tree, 99)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
```

</details>

### internal node deletion

#### deletes key from internal node using predecessor

1. var tree = make tree
2. delete key
   - Expected: has(tree, 30) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50])
delete_key(tree, 30)
expect(has(tree, 30)).to_equal(false)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

### BTree rebalancing

### borrow_from_left

#### borrows from left sibling when right child underflows

1. var tree = make tree
2. delete key
3. delete key
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50, 60, 70])
delete_key(tree, 70)
delete_key(tree, 60)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

### borrow_from_right

#### borrows from right sibling when left child underflows

1. var tree = make tree
2. delete key
3. delete key
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true
   - Expected: has(tree, 60) is true
   - Expected: has(tree, 70) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50, 60, 70])
delete_key(tree, 10)
delete_key(tree, 20)
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
expect(has(tree, 60)).to_equal(true)
expect(has(tree, 70)).to_equal(true)
```

</details>

### merge_children

#### merges nodes when both siblings are at minimum

1. var tree = make tree
2. delete key
3. delete key
4. delete key
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50])
delete_key(tree, 10)
delete_key(tree, 50)
delete_key(tree, 30)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
```

</details>

#### merge reduces tree height when root becomes empty

1. var tree = make tree
2. delete key
3. delete key
4. delete key
5. delete key
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50])
delete_key(tree, 10)
delete_key(tree, 20)
delete_key(tree, 30)
delete_key(tree, 40)
expect(has(tree, 50)).to_equal(true)
```

</details>

### cascade rebalancing

#### handles multi-level rebalancing cascade

1. var tree = make tree
2. delete key
3. delete key
4. delete key
5. delete key
6. delete key
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([5, 10, 15, 20, 25, 30, 35, 40, 45, 50])
delete_key(tree, 5)
delete_key(tree, 15)
delete_key(tree, 25)
delete_key(tree, 35)
delete_key(tree, 45)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

### BTree order invariant

#### all surviving keys remain accessible after mixed delete

1. var tree = make tree
2. delete key
3. delete key
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true
   - Expected: has(tree, 70) is true
   - Expected: has(tree, 80) is true
   - Expected: has(tree, 30) is false
   - Expected: has(tree, 60) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([50, 30, 70, 10, 40, 60, 80, 20])
delete_key(tree, 30)
delete_key(tree, 60)
# Remaining: 10, 20, 40, 50, 70, 80
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
expect(has(tree, 70)).to_equal(true)
expect(has(tree, 80)).to_equal(true)
# Deleted keys must not be found
expect(has(tree, 30)).to_equal(false)
expect(has(tree, 60)).to_equal(false)
```

</details>

#### insert after delete maintains correctness

1. var tree = make tree
2. delete key
3. tree insert
4. tree insert
   - Expected: has(tree, 25) is true
   - Expected: has(tree, 35) is true
   - Expected: has(tree, 30) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = make_tree([10, 20, 30, 40, 50])
delete_key(tree, 30)
tree.insert(k(25), "v25")
tree.insert(k(35), "v35")
expect(has(tree, 25)).to_equal(true)
expect(has(tree, 35)).to_equal(true)
expect(has(tree, 30)).to_equal(false)
# Original survivors still present
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
