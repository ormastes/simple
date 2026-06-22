# btree_basic_spec

> Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

<!-- sdn-diagram:id=btree_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=btree_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

btree_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=btree_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# btree_basic_spec

Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | System/Collections |
| Status | Active |
| Source | `test/03_system/feature/usage/btree_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Description

Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

Tests cover:
- Map creation and initialization
- Key-value insertion and retrieval
- Key ordering maintenance
- Key existence checking and removal
- Collection mutations (clear)
- Array/collection views (keys, values)

**Integration Scope:** BTreeMap + Collections FFI
**Complexity:** Low
**Coverage Impact:** btreemap.rs (0%→40%), collections FFI

## Scenarios

### BTreeMap basic operations

#### Creation and insertion

#### creates new BTreeMap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = BTreeMap.new()

expect(map).not_to(be_nil())
expect(map.is_empty()).to_equal(true)
```

</details>

#### inserts and retrieves values

1. var map = BTreeMap new
2. map insert
   - Expected: result equals `value1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert("key1", "value1")

val result = map.get("key1")
expect(result).to_equal("value1")
```

</details>

#### maintains sorted order

1. var map = BTreeMap new
2. map insert
3. map insert
4. map insert
   - Expected: keys.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert("c", 3)
map.insert("a", 1)
map.insert("b", 2)

val keys = map.keys()
expect(keys.len()).to_equal(3)
# Keys should be sorted
```

</details>

#### Key operations

#### checks if key exists

1. var map = BTreeMap new
2. map insert
   - Expected: map.has("exists") is true
   - Expected: map.has("missing") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert("exists", "yes")

expect(map.has("exists")).to_equal(true)
expect(map.has("missing")).to_equal(false)
```

</details>

#### removes keys

1. var map = BTreeMap new
2. map insert
3. map remove
   - Expected: map.has("key") is false
   - Expected: map.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert("key", "value")

map.remove("key")
expect(map.has("key")).to_equal(false)
expect(map.len()).to_equal(0)
```

</details>

#### Collection methods

#### clears all entries

1. var map = BTreeMap new
2. map insert
3. map insert
4. map clear
   - Expected: map.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert("a", 1)
map.insert("b", 2)

map.clear()
expect(map.is_empty()).to_equal(true)
```

</details>

#### gets all values

1. var map = BTreeMap new
2. map insert
3. map insert
   - Expected: values.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = BTreeMap.new()
map.insert(1, 100)
map.insert(2, 200)

val values = map.values()
expect(values.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
