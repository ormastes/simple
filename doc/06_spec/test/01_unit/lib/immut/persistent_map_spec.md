# Persistent Map Specification

> <details>

<!-- sdn-diagram:id=persistent_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_map_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Map Specification

## Scenarios

### PersistentMap

### empty map

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.is_empty()).to_equal(true)
```

</details>

#### get returns nil for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.get("key")).to_be_nil()
expect(m.get("anything")).to_be_nil()
```

</details>

#### contains returns false for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.contains("x")).to_equal(false)
```

</details>

#### keys returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val k = m.keys()
expect(k.len()).to_equal(0)
```

</details>

#### values returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val v = m.values()
expect(v.len()).to_equal(0)
```

</details>

#### entries returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val e = m.entries()
expect(e.len()).to_equal(0)
```

</details>

### set and get

#### stores and retrieves a single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1)
expect(m.get("a")).to_equal(1)
expect(m.len()).to_equal(1)
```

</details>

#### returns new map on set - original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty()
val m2 = m1.set("a", 1)
expect(m1.len()).to_equal(0)
expect(m1.get("a")).to_be_nil()
expect(m2.len()).to_equal(1)
expect(m2.get("a")).to_equal(1)
```

</details>

#### overwrites existing key with same length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("a", 2)
expect(m.get("a")).to_equal(2)
expect(m.len()).to_equal(1)
```

</details>

#### handles two keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
expect(m.len()).to_equal(2)
```

</details>

#### handles three keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
expect(m.get("c")).to_equal(3)
expect(m.len()).to_equal(3)
```

</details>

#### stores text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("name", "Alice")
expect(m.get("name")).to_equal("Alice")
```

</details>

#### stores integer keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set(1, "one").set(2, "two")
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1)
expect(m.get("b")).to_be_nil()
```

</details>

#### is no longer empty after set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 42)
expect(m.is_empty()).to_equal(false)
```

</details>

### persistence across multiple sets

#### preserves snapshots

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0 = PersistentMap.empty()
val m1 = m0.set("a", 1)
val m2 = m1.set("b", 2)
val m3 = m2.set("c", 3)
expect(m0.len()).to_equal(0)
expect(m1.len()).to_equal(1)
expect(m2.len()).to_equal(2)
expect(m3.len()).to_equal(3)
expect(m1.get("b")).to_be_nil()
expect(m2.get("c")).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("key", "old")
val m2 = m1.set("key", "new")
expect(m1.get("key")).to_equal("old")
expect(m2.get("key")).to_equal("new")
```

</details>

### remove

#### removes an existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val m2 = m.remove("a")
expect(m2.get("a")).to_be_nil()
expect(m2.get("b")).to_equal(2)
expect(m2.len()).to_equal(1)
```

</details>

#### does not modify original on remove

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1)
val m2 = m1.remove("a")
expect(m1.get("a")).to_equal(1)
expect(m1.len()).to_equal(1)
expect(m2.get("a")).to_be_nil()
expect(m2.len()).to_equal(0)
```

</details>

#### handles removing non-existent key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1)
val m2 = m.remove("b")
expect(m2.len()).to_equal(1)
expect(m2.get("a")).to_equal(1)
```

</details>

#### removes last key to get empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("only", 99)
val m2 = m.remove("only")
expect(m2.len()).to_equal(0)
expect(m2.is_empty()).to_equal(true)
```

</details>

#### removes from multi-key map

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val m2 = m.remove("b")
expect(m2.len()).to_equal(2)
expect(m2.get("a")).to_equal(1)
expect(m2.get("b")).to_be_nil()
expect(m2.get("c")).to_equal(3)
```

</details>

### contains

#### returns true for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 42)
expect(m.contains("x")).to_equal(true)
```

</details>

#### returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 42)
expect(m.contains("y")).to_equal(false)
```

</details>

#### returns false after removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 42).remove("x")
expect(m.contains("x")).to_equal(false)
```

</details>

### get_or

#### returns default for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.get_or("x", 42)).to_equal(42)
```

</details>

#### returns value for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 10)
expect(m.get_or("x", 42)).to_equal(10)
```

</details>

#### returns default with text fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
expect(m.get_or("name", "unknown")).to_equal("unknown")
```

</details>

### from_entries

#### builds from key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.from_entries([["a", 1], ["b", 2]])
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
expect(m.len()).to_equal(2)
```

</details>

#### handles empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.from_entries([])
expect(m.len()).to_equal(0)
expect(m.is_empty()).to_equal(true)
```

</details>

#### handles single entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.from_entries([["only", 99]])
expect(m.get("only")).to_equal(99)
expect(m.len()).to_equal(1)
```

</details>

#### last value wins for duplicate keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.from_entries([["a", 1], ["a", 2]])
expect(m.get("a")).to_equal(2)
expect(m.len()).to_equal(1)
```

</details>

### from_dict

#### builds from mutable dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {}
d["x"] = 10
d["y"] = 20
val m = PersistentMap.from_dict(d)
expect(m.get("x")).to_equal(10)
expect(m.get("y")).to_equal(20)
expect(m.len()).to_equal(2)
```

</details>

#### handles empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {}
val m = PersistentMap.from_dict(d)
expect(m.len()).to_equal(0)
```

</details>

### keys and values

#### returns correct number of keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 1).set("y", 2)
val k = m.keys()
expect(k.len()).to_equal(2)
```

</details>

#### returns correct number of values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 10).set("y", 20)
val v = m.values()
expect(v.len()).to_equal(2)
```

</details>

#### single key map

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("only", 42)
val k = m.keys()
val v = m.values()
expect(k.len()).to_equal(1)
expect(v.len()).to_equal(1)
```

</details>

### entries

#### returns key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1)
val e = m.entries()
expect(e.len()).to_equal(1)
val pair = e[0]
expect(pair[0]).to_equal("a")
expect(pair[1]).to_equal(1)
```

</details>

#### returns correct count for multi-entry map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val e = m.entries()
expect(e.len()).to_equal(3)
```

</details>

### merge

#### merges two disjoint maps

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(1)
expect(merged.get("b")).to_equal(2)
expect(merged.len()).to_equal(2)
```

</details>

#### other takes precedence on conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("a", 99)
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(99)
expect(merged.len()).to_equal(1)
```

</details>

#### merge with empty returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty()
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(1)
expect(merged.len()).to_equal(1)
```

</details>

#### empty merge with other returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty()
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(merged.get("b")).to_equal(2)
expect(merged.len()).to_equal(1)
```

</details>

#### does not modify originals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(m1.len()).to_equal(1)
expect(m2.len()).to_equal(1)
expect(merged.len()).to_equal(2)
```

</details>

### filter

#### keeps entries matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val filtered = m.filter(fn(k, v): v > 1)
expect(filtered.len()).to_equal(2)
expect(filtered.get("a")).to_be_nil()
expect(filtered.get("b")).to_equal(2)
expect(filtered.get("c")).to_equal(3)
```

</details>

#### returns empty when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val filtered = m.filter(fn(k, v): v > 100)
expect(filtered.len()).to_equal(0)
expect(filtered.is_empty()).to_equal(true)
```

</details>

#### returns all when everything matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val filtered = m.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)
```

</details>

### map_values

#### transforms all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val doubled = m.map_values(fn(v): v * 2)
expect(doubled.get("a")).to_equal(2)
expect(doubled.get("b")).to_equal(4)
expect(doubled.len()).to_equal(2)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 5)
val mapped = m.map_values(fn(v): v + 10)
expect(m.get("a")).to_equal(5)
expect(mapped.get("a")).to_equal(15)
```

</details>

### fold

#### sums all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val total = m.fold(0, fn(acc, k, v): acc + v)
expect(total).to_equal(6)
```

</details>

#### fold over empty returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val result = m.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)
```

</details>

### update

#### updates existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("count", 5)
val m2 = m.update("count", fn(v): v + 1)
expect(m2.get("count")).to_equal(6)
expect(m.get("count")).to_equal(5)
```

</details>

#### creates key when missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val m2 = m.update("new", fn(v): 42)
expect(m2.get("new")).to_equal(42)
```

</details>

### copy

#### returns identical map

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val c = m.copy()
expect(c.get("a")).to_equal(1)
expect(c.get("b")).to_equal(2)
expect(c.len()).to_equal(2)
```

</details>

### to_dict

#### converts to mutable dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("x", 10).set("y", 20)
val d = m.to_dict()
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
```

</details>

#### empty map converts to empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val d = m.to_dict()
expect(d.len()).to_equal(0)
```

</details>

### stress test

#### handles many elements via helper fn

1. fn run stress
2. var m = PersistentMap empty
3. m = m set
4. m len
   - Expected: run_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_stress() -> i64:
    var m = PersistentMap.empty()
    var i = 0
    while i < 100:
        m = m.set("key_{i}", i)
        i = i + 1
    m.len()
expect(run_stress()).to_equal(100)
```

</details>

#### set and get many elements

1. fn run get stress
2. var m = PersistentMap empty
3. m = m set
   - Expected: run_get_stress() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_get_stress() -> i64:
    var m = PersistentMap.empty()
    var i = 0
    while i < 50:
        m = m.set("k_{i}", i * 10)
        i = i + 1
    var ok_count = 0
    i = 0
    while i < 50:
        val v = m.get("k_{i}")
        if v == i * 10:
            ok_count = ok_count + 1
        i = i + 1
    ok_count
expect(run_get_stress()).to_equal(50)
```

</details>

#### remove many elements

1. fn run remove stress
2. var m = PersistentMap empty
3. m = m set
4. m = m remove
5. m len
   - Expected: run_remove_stress() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_remove_stress() -> i64:
    var m = PersistentMap.empty()
    var i = 0
    while i < 30:
        m = m.set("r_{i}", i)
        i = i + 1
    i = 0
    while i < 15:
        m = m.remove("r_{i}")
        i = i + 1
    m.len()
expect(run_remove_stress()).to_equal(15)
```

</details>

### edge cases

#### set same key same value returns same map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("a", 1)
val m2 = m.set("a", 1)
expect(m2.get("a")).to_equal(1)
expect(m2.len()).to_equal(1)
```

</details>

#### empty key string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("", "empty_key")
expect(m.get("")).to_equal("empty_key")
expect(m.len()).to_equal(1)
```

</details>

#### nil value stored and retrieved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty().set("nil_val", nil)
expect(m.len()).to_equal(1)
```

</details>

#### remove from empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentMap.empty()
val m2 = m.remove("nothing")
expect(m2.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/persistent_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentMap
- empty map
- set and get
- persistence across multiple sets
- remove
- contains
- get_or
- from_entries
- from_dict
- keys and values
- entries
- merge
- filter
- map_values
- fold
- update
- copy
- to_dict
- stress test
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
