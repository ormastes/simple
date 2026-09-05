# Persistent Sorted Map Specification

> <details>

<!-- sdn-diagram:id=persistent_sorted_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_sorted_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_sorted_map_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_sorted_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 88 | 88 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Sorted Map Specification

## Scenarios

### PersistentSortedMap

### empty map

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.is_empty()).to_equal(true)
```

</details>

#### get returns nil for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.get(1)).to_be_nil()
expect(m.get(999)).to_be_nil()
```

</details>

#### get_or returns default for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.get_or(1, 42)).to_equal(42)
```

</details>

#### contains returns false for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.contains(1)).to_equal(false)
```

</details>

#### min_key returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.min_key()).to_be_nil()
```

</details>

#### max_key returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.max_key()).to_be_nil()
```

</details>

#### min_entry returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.min_entry()).to_be_nil()
```

</details>

#### max_entry returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.max_entry()).to_be_nil()
```

</details>

#### keys returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.keys().len()).to_equal(0)
```

</details>

#### values returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.values().len()).to_equal(0)
```

</details>

#### entries returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.entries().len()).to_equal(0)
```

</details>

### set and get

#### stores and retrieves a single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "five")
expect(m.get(5)).to_equal("five")
expect(m.len()).to_equal(1)
```

</details>

#### returns new map on set - original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints()
val m2 = m1.set(1, "one")
expect(m1.len()).to_equal(0)
expect(m1.get(1)).to_be_nil()
expect(m2.len()).to_equal(1)
expect(m2.get(1)).to_equal("one")
```

</details>

#### overwrites existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = m1.set(1, "new")
expect(m2.get(1)).to_equal("new")
expect(m2.len()).to_equal(1)
```

</details>

#### handles two keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "one").set(2, "two")
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
expect(m.len()).to_equal(2)
```

</details>

#### handles three keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
expect(m.get(1)).to_equal("a")
expect(m.get(2)).to_equal("b")
expect(m.get(3)).to_equal("c")
expect(m.len()).to_equal(3)
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "one")
expect(m.get(99)).to_be_nil()
```

</details>

#### is no longer empty after set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "x")
expect(m.is_empty()).to_equal(false)
```

</details>

### text keys

#### stores and retrieves text keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_text().set("apple", 1).set("banana", 2)
expect(m.get("apple")).to_equal(1)
expect(m.get("banana")).to_equal(2)
expect(m.len()).to_equal(2)
```

</details>

#### maintains lexicographic order for text keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_text().set("cherry", 3).set("apple", 1).set("banana", 2)
val k = m.keys()
expect(k[0]).to_equal("apple")
expect(k[1]).to_equal("banana")
expect(k[2]).to_equal("cherry")
```

</details>

### contains

#### returns true for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(10, "ten")
expect(m.contains(10)).to_equal(true)
```

</details>

#### returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(10, "ten")
expect(m.contains(20)).to_equal(false)
```

</details>

#### returns false after removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(10, "ten").remove(10)
expect(m.contains(10)).to_equal(false)
```

</details>

### get_or

#### returns value for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "one")
expect(m.get_or(1, "default")).to_equal("one")
```

</details>

#### returns default for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.get_or(1, "default")).to_equal("default")
```

</details>

#### returns default with numeric fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.get_or(99, -1)).to_equal(-1)
```

</details>

### persistence

#### preserves snapshots across multiple sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0 = PersistentSortedMap.of_ints()
val m1 = m0.set(1, "a")
val m2 = m1.set(2, "b")
val m3 = m2.set(3, "c")
expect(m0.len()).to_equal(0)
expect(m1.len()).to_equal(1)
expect(m2.len()).to_equal(2)
expect(m3.len()).to_equal(3)
expect(m1.get(2)).to_be_nil()
expect(m2.get(3)).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = m1.set(1, "new")
expect(m1.get(1)).to_equal("old")
expect(m2.get(1)).to_equal("new")
```

</details>

#### remove does not affect earlier version

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "a").set(2, "b")
val m2 = m1.remove(1)
expect(m1.get(1)).to_equal("a")
expect(m1.len()).to_equal(2)
expect(m2.get(1)).to_be_nil()
expect(m2.len()).to_equal(1)
```

</details>

### remove

#### removes an existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b")
val m2 = m.remove(1)
expect(m2.get(1)).to_be_nil()
expect(m2.get(2)).to_equal("b")
expect(m2.len()).to_equal(1)
```

</details>

#### handles removing non-existent key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a")
val m2 = m.remove(99)
expect(m2.len()).to_equal(1)
expect(m2.get(1)).to_equal("a")
```

</details>

#### removes last key to get empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "only")
val m2 = m.remove(1)
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
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val m2 = m.remove(2)
expect(m2.len()).to_equal(2)
expect(m2.get(1)).to_equal("a")
expect(m2.get(2)).to_be_nil()
expect(m2.get(3)).to_equal("c")
```

</details>

#### remove from empty map returns same empty map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
val m2 = m.remove(1)
expect(m2.len()).to_equal(0)
```

</details>

### min and max

#### min_key returns smallest key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i")
expect(m.min_key()).to_equal(1)
```

</details>

#### max_key returns largest key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i")
expect(m.max_key()).to_equal(9)
```

</details>

#### min_entry returns key-value pair for smallest key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "five").set(1, "one").set(9, "nine")
val entry = m.min_entry()
expect(entry[0]).to_equal(1)
expect(entry[1]).to_equal("one")
```

</details>

#### max_entry returns key-value pair for largest key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "five").set(1, "one").set(9, "nine")
val entry = m.max_entry()
expect(entry[0]).to_equal(9)
expect(entry[1]).to_equal("nine")
```

</details>

#### single element map has same min and max

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(42, "answer")
expect(m.min_key()).to_equal(42)
expect(m.max_key()).to_equal(42)
```

</details>

### range

#### returns entries within range inclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e").set(7, "g").set(9, "i")
val r = m.range(3, 7)
expect(r.len()).to_equal(3)
expect(r[0][0]).to_equal(3)
expect(r[1][0]).to_equal(5)
expect(r[2][0]).to_equal(7)
```

</details>

#### returns empty for range with no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(10, "j")
val r = m.range(3, 7)
expect(r.len()).to_equal(0)
```

</details>

#### returns single entry when from equals to

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val r = m.range(3, 3)
expect(r.len()).to_equal(1)
expect(r[0][0]).to_equal(3)
```

</details>

#### range on empty map returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
val r = m.range(1, 10)
expect(r.len()).to_equal(0)
```

</details>

#### returns all entries when range covers entire map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(2, "b").set(4, "d").set(6, "f")
val r = m.range(1, 10)
expect(r.len()).to_equal(3)
```

</details>

### floor

#### returns exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val f = m.floor(3)
expect(f[0]).to_equal(3)
expect(f[1]).to_equal("c")
```

</details>

#### returns greatest key less than target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val f = m.floor(4)
expect(f[0]).to_equal(3)
expect(f[1]).to_equal("c")
```

</details>

#### returns nil when no key is less or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "e").set(10, "j")
val f = m.floor(3)
expect(f).to_be_nil()
```

</details>

#### floor on empty map returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.floor(5)).to_be_nil()
```

</details>

### ceiling

#### returns exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val c = m.ceiling(3)
expect(c[0]).to_equal(3)
expect(c[1]).to_equal("c")
```

</details>

#### returns smallest key greater than target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val c = m.ceiling(2)
expect(c[0]).to_equal(3)
expect(c[1]).to_equal("c")
```

</details>

#### returns nil when no key is greater or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c")
val c = m.ceiling(10)
expect(c).to_be_nil()
```

</details>

#### ceiling on empty map returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.ceiling(5)).to_be_nil()
```

</details>

### ordered iteration

#### keys are in sorted order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i").set(3, "c")
val k = m.keys()
expect(k.len()).to_equal(4)
expect(k[0]).to_equal(1)
expect(k[1]).to_equal(3)
expect(k[2]).to_equal(5)
expect(k[3]).to_equal(9)
```

</details>

#### values are in key-sorted order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
val v = m.values()
expect(v[0]).to_equal("a")
expect(v[1]).to_equal("b")
expect(v[2]).to_equal("c")
```

</details>

#### entries are in key-sorted order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(20, "x").set(10, "y").set(30, "z")
val e = m.entries()
expect(e.len()).to_equal(3)
expect(e[0][0]).to_equal(10)
expect(e[1][0]).to_equal(20)
expect(e[2][0]).to_equal(30)
```

</details>

### merge

#### merges two disjoint maps

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "a").set(3, "c")
val m2 = PersistentSortedMap.of_ints().set(2, "b").set(4, "d")
val merged = m1.merge(m2)
expect(merged.len()).to_equal(4)
expect(merged.get(1)).to_equal("a")
expect(merged.get(2)).to_equal("b")
expect(merged.get(3)).to_equal("c")
expect(merged.get(4)).to_equal("d")
```

</details>

#### other takes precedence on conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = PersistentSortedMap.of_ints().set(1, "new")
val merged = m1.merge(m2)
expect(merged.get(1)).to_equal("new")
expect(merged.len()).to_equal(1)
```

</details>

#### merge with empty returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "a")
val m2 = PersistentSortedMap.of_ints()
val merged = m1.merge(m2)
expect(merged.get(1)).to_equal("a")
expect(merged.len()).to_equal(1)
```

</details>

#### empty merge with other returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints()
val m2 = PersistentSortedMap.of_ints().set(2, "b")
val merged = m1.merge(m2)
expect(merged.get(2)).to_equal("b")
expect(merged.len()).to_equal(1)
```

</details>

#### does not modify originals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(1, "a")
val m2 = PersistentSortedMap.of_ints().set(2, "b")
val merged = m1.merge(m2)
expect(m1.len()).to_equal(1)
expect(m2.len()).to_equal(1)
expect(merged.len()).to_equal(2)
```

</details>

#### merged map maintains sorted order

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = PersistentSortedMap.of_ints().set(5, "e").set(1, "a")
val m2 = PersistentSortedMap.of_ints().set(3, "c").set(7, "g")
val merged = m1.merge(m2)
val k = merged.keys()
expect(k[0]).to_equal(1)
expect(k[1]).to_equal(3)
expect(k[2]).to_equal(5)
expect(k[3]).to_equal(7)
```

</details>

### filter

#### keeps entries matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20).set(3, 30)
val filtered = m.filter(fn(k, v): v > 15)
expect(filtered.len()).to_equal(2)
expect(filtered.get(1)).to_be_nil()
expect(filtered.get(2)).to_equal(20)
expect(filtered.get(3)).to_equal(30)
```

</details>

#### returns empty when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
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
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
val filtered = m.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)
```

</details>

#### filter by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val filtered = m.filter(fn(k, v): k > 1)
expect(filtered.len()).to_equal(2)
expect(filtered.contains(1)).to_equal(false)
expect(filtered.contains(2)).to_equal(true)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
val filtered = m.filter(fn(k, v): v > 15)
expect(m.len()).to_equal(2)
expect(filtered.len()).to_equal(1)
```

</details>

### fold

#### sums all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20).set(3, 30)
val total = m.fold(0, fn(acc, k, v): acc + v)
expect(total).to_equal(60)
```

</details>

#### fold over empty returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
val result = m.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)
```

</details>

#### fold processes keys in sorted order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
val result = m.fold("", fn(acc, k, v): acc + v)
expect(result).to_equal("abc")
```

</details>

#### fold counts entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val count = m.fold(0, fn(acc, k, v): acc + 1)
expect(count).to_equal(3)
```

</details>

### from_entries

#### builds from key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.from_entries([[1, "one"], [2, "two"]], compare_ints)
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
expect(m.len()).to_equal(2)
```

</details>

#### handles empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.from_entries([], compare_ints)
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
val m = PersistentSortedMap.from_entries([[42, "answer"]], compare_ints)
expect(m.get(42)).to_equal("answer")
expect(m.len()).to_equal(1)
```

</details>

#### last value wins for duplicate keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.from_entries([[1, "first"], [1, "second"]], compare_ints)
expect(m.get(1)).to_equal("second")
expect(m.len()).to_equal(1)
```

</details>

#### maintains sorted order from entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.from_entries([[5, "e"], [1, "a"], [3, "c"]], compare_ints)
val k = m.keys()
expect(k[0]).to_equal(1)
expect(k[1]).to_equal(3)
expect(k[2]).to_equal(5)
```

</details>

### to_dict

#### converts to mutable dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "one").set(2, "two")
val d = m.to_dict()
expect(d[1]).to_equal("one")
expect(d[2]).to_equal("two")
```

</details>

#### empty map converts to empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
val d = m.to_dict()
expect(d.len()).to_equal(0)
```

</details>

### factory functions

#### of_ints creates empty int map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints()
expect(m.len()).to_equal(0)
val m2 = m.set(1, "one")
expect(m2.get(1)).to_equal("one")
```

</details>

#### of_text creates empty text map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_text()
expect(m.len()).to_equal(0)
val m2 = m.set("hello", 1)
expect(m2.get("hello")).to_equal(1)
```

</details>

#### empty with custom comparator

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.empty(compare_ints)
val m2 = m.set(3, "c").set(1, "a").set(2, "b")
val k = m2.keys()
expect(k[0]).to_equal(1)
expect(k[1]).to_equal(2)
expect(k[2]).to_equal(3)
```

</details>

### stress test

#### handles many insertions via helper fn

- fn run insert stress
- var m = PersistentSortedMap of ints
- m = m set
- m len
   - Expected: run_insert_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_insert_stress() -> i64:
    var m = PersistentSortedMap.of_ints()
    var i = 0
    while i < 100:
        m = m.set(i, i * 10)
        i = i + 1
    m.len()
expect(run_insert_stress()).to_equal(100)
```

</details>

#### set and get many elements

- fn run get stress
- var m = PersistentSortedMap of ints
- m = m set
   - Expected: run_get_stress() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_get_stress() -> i64:
    var m = PersistentSortedMap.of_ints()
    var i = 0
    while i < 50:
        m = m.set(i, i * 10)
        i = i + 1
    var ok_count = 0
    i = 0
    while i < 50:
        val v = m.get(i)
        if v == i * 10:
            ok_count = ok_count + 1
        i = i + 1
    ok_count
expect(run_get_stress()).to_equal(50)
```

</details>

#### remove many elements

- fn run remove stress
- var m = PersistentSortedMap of ints
- m = m set
- m = m remove
- m len
   - Expected: run_remove_stress() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_remove_stress() -> i64:
    var m = PersistentSortedMap.of_ints()
    var i = 0
    while i < 30:
        m = m.set(i, i)
        i = i + 1
    i = 0
    while i < 15:
        m = m.remove(i)
        i = i + 1
    m.len()
expect(run_remove_stress()).to_equal(15)
```

</details>

#### keys stay sorted after many random-order inserts

- fn run order stress
- var m = PersistentSortedMap of ints
- m = m set
- m = m set
- m = m set
- m = m set
- m = m set
- m = m set
- m = m set
- m = m set
- m = m set
   - Expected: run_order_stress() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_order_stress() -> bool:
    var m = PersistentSortedMap.of_ints()
    # Insert in non-sequential order
    m = m.set(50, "a")
    m = m.set(10, "b")
    m = m.set(90, "c")
    m = m.set(30, "d")
    m = m.set(70, "e")
    m = m.set(20, "f")
    m = m.set(80, "g")
    m = m.set(40, "h")
    m = m.set(60, "i")
    val k = m.keys()
    var sorted = true
    var idx = 1
    while idx < k.len():
        if k[idx] < k[idx - 1]:
            sorted = false
        idx = idx + 1
    sorted
expect(run_order_stress()).to_equal(true)
```

</details>

### edge cases

#### set same key same value returns equivalent map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(1, "a")
val m2 = m.set(1, "a")
expect(m2.get(1)).to_equal("a")
expect(m2.len()).to_equal(1)
```

</details>

#### single entry map operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(42, "answer")
expect(m.len()).to_equal(1)
expect(m.min_key()).to_equal(42)
expect(m.max_key()).to_equal(42)
val r = m.range(1, 100)
expect(r.len()).to_equal(1)
val f = m.floor(42)
expect(f[0]).to_equal(42)
val c = m.ceiling(42)
expect(c[0]).to_equal(42)
```

</details>

#### negative integer keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = PersistentSortedMap.of_ints().set(-5, "neg5").set(0, "zero").set(5, "pos5")
expect(m.get(-5)).to_equal("neg5")
expect(m.min_key()).to_equal(-5)
expect(m.max_key()).to_equal(5)
val k = m.keys()
expect(k[0]).to_equal(-5)
expect(k[1]).to_equal(0)
expect(k[2]).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentSortedMap
- empty map
- set and get
- text keys
- contains
- get_or
- persistence
- remove
- min and max
- range
- floor
- ceiling
- ordered iteration
- merge
- filter
- fold
- from_entries
- to_dict
- factory functions
- stress test
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 88 |
| Active scenarios | 88 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
