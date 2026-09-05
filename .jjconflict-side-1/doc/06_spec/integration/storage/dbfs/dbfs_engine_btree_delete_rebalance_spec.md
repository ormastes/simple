# BTree Delete Rebalancing Specification

> Tests the CLRS top-down proactive fix-up for BTree deletion:

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
| Status | Implemented — CLRS proactive fix-up is in `btree.spl`. |
| Source | `test/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl` |
| Updated | 2026-08-26 |
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

- removes a key from a single-node tree
   - Expected: has(tree, 20) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("removes a key from a single-node tree")
var tree = make_tree([10, 20, 30])
tree.delete(k(20))
expect(has(tree, 20)).to_equal(false)
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
```

</details>

#### removes all keys leaving empty tree

- removes all keys leaving empty tree
   - Expected: has(tree, 5) is false
   - Expected: has(tree, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("removes all keys leaving empty tree")
var tree = make_tree([5, 10])
tree.delete(k(5))
tree.delete(k(10))
expect(has(tree, 5)).to_equal(false)
expect(has(tree, 10)).to_equal(false)
```

</details>

#### delete of nonexistent key is a no-op

- delete of nonexistent key is a no-op
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("delete of nonexistent key is a no-op")
var tree = make_tree([10, 20, 30])
tree.delete(k(99))
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
```

</details>

### internal node deletion

#### deletes key from internal node using predecessor

- deletes key from internal node using predecessor
   - Expected: has(tree, 30) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deletes key from internal node using predecessor")
var tree = make_tree([10, 20, 30, 40, 50])
tree.delete(k(30))
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

- borrows from left sibling when right child underflows
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("borrows from left sibling when right child underflows")
var tree = make_tree([10, 20, 30, 40, 50, 60, 70])
tree.delete(k(70))
tree.delete(k(60))
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

### borrow_from_right

#### borrows from right sibling when left child underflows

- borrows from right sibling when left child underflows
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true
   - Expected: has(tree, 60) is true
   - Expected: has(tree, 70) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("borrows from right sibling when left child underflows")
var tree = make_tree([10, 20, 30, 40, 50, 60, 70])
tree.delete(k(10))
tree.delete(k(20))
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
expect(has(tree, 60)).to_equal(true)
expect(has(tree, 70)).to_equal(true)
```

</details>

### merge_children

#### merges nodes when both siblings are at minimum

- merges nodes when both siblings are at minimum
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("merges nodes when both siblings are at minimum")
var tree = make_tree([10, 20, 30, 40, 50])
tree.delete(k(10))
tree.delete(k(50))
tree.delete(k(30))
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
```

</details>

#### merge reduces tree height when root becomes empty

- merge reduces tree height when root becomes empty
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("merge reduces tree height when root becomes empty")
var tree = make_tree([10, 20, 30, 40, 50])
tree.delete(k(10))
tree.delete(k(20))
tree.delete(k(30))
tree.delete(k(40))
expect(has(tree, 50)).to_equal(true)
```

</details>

### cascade rebalancing

#### handles multi-level rebalancing cascade

- handles multi-level rebalancing cascade
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 30) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles multi-level rebalancing cascade")
var tree = make_tree([5, 10, 15, 20, 25, 30, 35, 40, 45, 50])
tree.delete(k(5))
tree.delete(k(15))
tree.delete(k(25))
tree.delete(k(35))
tree.delete(k(45))
expect(has(tree, 10)).to_equal(true)
expect(has(tree, 20)).to_equal(true)
expect(has(tree, 30)).to_equal(true)
expect(has(tree, 40)).to_equal(true)
expect(has(tree, 50)).to_equal(true)
```

</details>

### BTree order invariant

#### all surviving keys remain accessible after mixed delete

- all surviving keys remain accessible after mixed delete
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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("all surviving keys remain accessible after mixed delete")
var tree = make_tree([50, 30, 70, 10, 40, 60, 80, 20])
tree.delete(k(30))
tree.delete(k(60))
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

- insert after delete maintains correctness
   - Expected: has(tree, 25) is true
   - Expected: has(tree, 35) is true
   - Expected: has(tree, 30) is false
   - Expected: has(tree, 10) is true
   - Expected: has(tree, 20) is true
   - Expected: has(tree, 40) is true
   - Expected: has(tree, 50) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("insert after delete maintains correctness")
var tree = make_tree([10, 20, 30, 40, 50])
tree.delete(k(30))
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7273d91e63df3e0a523e2ce1048e97cfdc02a00d6341d85f01ba008bc98cb9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7273d91e63df3e0a523e2ce1048e97cfdc02a00d6341d85f01ba008bc98cb9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7273d91e63df3e0a523e2ce1048e97cfdc02a00d6341d85f01ba008bc98cb9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes a key from a single-node tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes all keys leaving empty tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delete of nonexistent key is a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
