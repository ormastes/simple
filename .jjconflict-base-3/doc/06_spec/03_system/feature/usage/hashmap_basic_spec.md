# HashMap Basic Operations Specification

> HashMap + Collections FFI

<!-- sdn-diagram:id=hashmap_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hashmap_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hashmap_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hashmap_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HashMap Basic Operations Specification

HashMap + Collections FFI

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/03_system/feature/usage/hashmap_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Integration Scope

HashMap + Collections FFI

## Complexity

Low

## Coverage Impact

hashmap.rs (0%→40%), collections FFI

## Scenarios

### HashMap Basic Operations

### Creation and insertion

#### creates new HashMap

1. var map = HashMap new
   - Expected: map.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()

expect(map).not_to(be_nil())
expect(map.is_empty()).to_equal(true)
```

</details>

#### inserts and retrieves values

1. var map = HashMap new
2. map insert
   - Expected: result equals `value1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("key1", "value1")

val result = map.get("key1")
expect(result).to_equal("value1")
```

</details>

#### handles multiple insertions

1. var map = HashMap new
2. map insert
3. map insert
4. map insert
   - Expected: map.len() equals `3`
   - Expected: map.get("a") equals `1`
   - Expected: map.get("b") equals `2`
   - Expected: map.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("a", 1)
map.insert("b", 2)
map.insert("c", 3)

expect(map.len()).to_equal(3)
expect(map.get("a")).to_equal(1)
expect(map.get("b")).to_equal(2)
expect(map.get("c")).to_equal(3)
```

</details>

### Key operations

#### checks if key exists

1. var map = HashMap new
2. map insert
   - Expected: map.has("exists") is true
   - Expected: map.has("missing") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("exists", "yes")

expect(map.has("exists")).to_equal(true)
expect(map.has("missing")).to_equal(false)
```

</details>

#### removes keys

1. var map = HashMap new
2. map insert
3. map remove
   - Expected: map.has("key") is false
   - Expected: map.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("key", "value")

map.remove("key")
expect(map.has("key")).to_equal(false)
expect(map.len()).to_equal(0)
```

</details>

#### gets all keys

1. var map = HashMap new
2. map insert
3. map insert
   - Expected: keys.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("k1", "v1")
map.insert("k2", "v2")

val keys = map.keys()
expect(keys.len()).to_equal(2)
```

</details>

### Collection methods

#### clears all entries

1. var map = HashMap new
2. map insert
3. map insert
4. map clear
   - Expected: map.is_empty() is true
   - Expected: map.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("a", 1)
map.insert("b", 2)

map.clear()
expect(map.is_empty()).to_equal(true)
expect(map.len()).to_equal(0)
```

</details>

#### gets all values

1. var map = HashMap new
2. map insert
3. map insert
   - Expected: values.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
map.insert("k1", 100)
map.insert("k2", 200)

val values = map.values()
expect(values.len()).to_equal(2)
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
