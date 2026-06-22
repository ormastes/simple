# dbfs_engine_btree_spec

> DBFS B-Tree Specification

<!-- sdn-diagram:id=dbfs_engine_btree_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_btree_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_btree_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_btree_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_btree_spec

DBFS B-Tree Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_btree_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS B-Tree Specification

Verifies the generic B-tree used for namespace and metadata:
  1. insert + point-lookup round-trip
  2. range scan returns sorted results
  3. delete removes key
  4. MVCC snapshot read at older generation
  5. duplicate key insert updates existing value

## Scenarios

### DBFS B-Tree — insert and lookup
_Basic insert/lookup contract._

#### insert then lookup returns the same value

1. tree insert
   - Expected: got.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val key = NsDentryKey(parent_ino: 1, name_hash: 0x1234)
tree.insert(key, NsIno(value: 42)).unwrap()
val got = tree.lookup(key).unwrap()
expect(got.value).to_equal(42)
```

</details>

#### lookup on missing key returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val key = NsDentryKey(parent_ino: 99, name_hash: 0xDEAD)
val got = tree.lookup(key)
expect(got.is_none()).to_equal(true)
```

</details>

#### duplicate insert updates value

1. tree insert
2. tree insert
   - Expected: got.value equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val key = NsDentryKey(parent_ino: 1, name_hash: 0x01)
tree.insert(key, NsIno(value: 10)).unwrap()
tree.insert(key, NsIno(value: 20)).unwrap()
val got = tree.lookup(key).unwrap()
expect(got.value).to_equal(20)
```

</details>

### DBFS B-Tree — range scan
_Range scan returns all keys in [lo, hi]._

#### range scan returns entries in sorted order

1. tree insert
2. tree insert
3. tree insert
   - Expected: results.len() equals `3`
   - Expected: results[0].1.value equals `1`
   - Expected: results[2].1.value equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
tree.insert(NsDentryKey(parent_ino: 1, name_hash: 3), NsIno(value: 3)).unwrap()
tree.insert(NsDentryKey(parent_ino: 1, name_hash: 1), NsIno(value: 1)).unwrap()
tree.insert(NsDentryKey(parent_ino: 1, name_hash: 2), NsIno(value: 2)).unwrap()
val lo = NsDentryKey(parent_ino: 1, name_hash: 1)
val hi = NsDentryKey(parent_ino: 1, name_hash: 3)
val results = tree.range_scan(lo, hi).unwrap()
expect(results.len()).to_equal(3)
expect(results[0].1.value).to_equal(1)
expect(results[2].1.value).to_equal(3)
```

</details>

#### range scan with no matches returns empty list

1. tree insert
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
tree.insert(NsDentryKey(parent_ino: 1, name_hash: 100), NsIno(value: 1)).unwrap()
val lo = NsDentryKey(parent_ino: 1, name_hash: 200)
val hi = NsDentryKey(parent_ino: 1, name_hash: 300)
val results = tree.range_scan(lo, hi).unwrap()
expect(results.len()).to_equal(0)
```

</details>

### DBFS B-Tree — delete
_Delete removes the entry; subsequent lookup returns None._

#### delete then lookup returns None

1. tree insert
2. tree delete
   - Expected: got.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val key = NsDentryKey(parent_ino: 1, name_hash: 0x55)
tree.insert(key, NsIno(value: 7)).unwrap()
tree.delete(key).unwrap()
val got = tree.lookup(key)
expect(got.is_none()).to_equal(true)
```

</details>

#### delete missing key returns ok (idempotent)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val key = NsDentryKey(parent_ino: 5, name_hash: 0xFF)
val r = tree.delete(key)
expect(r.is_ok()).to_equal(true)
```

</details>

### DBFS B-Tree — MVCC snapshot
_Snapshot read at generation G sees only writes <= G._

#### snapshot at older gen does not see newer insert

1. tree insert
   - Expected: got.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = NsBTree.new()
val snap_gen: i64 = tree.current_gen()
val key = NsDentryKey(parent_ino: 1, name_hash: 0xAA)
tree.insert(key, NsIno(value: 99)).unwrap()
val got = tree.lookup_at_gen(key, snap_gen)
expect(got.is_none()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
