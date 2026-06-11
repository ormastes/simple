# Persistent Set Specification

> <details>

<!-- sdn-diagram:id=persistent_set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_set_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Set Specification

## Scenarios

### PersistentSet

### empty set

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
expect(s.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
expect(s.is_empty()).to_equal(true)
```

</details>

#### contains returns false for any element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
expect(s.contains("x")).to_equal(false)
expect(s.contains(42)).to_equal(false)
```

</details>

#### to_array returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
val arr = s.to_array()
expect(arr.len()).to_equal(0)
```

</details>

### add and contains

#### adds and finds a single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("alice")
expect(s.contains("alice")).to_equal(true)
expect(s.len()).to_equal(1)
```

</details>

#### returns new set on add - original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.empty()
val s2 = s1.add("alice")
expect(s1.len()).to_equal(0)
expect(s1.contains("alice")).to_equal(false)
expect(s2.len()).to_equal(1)
expect(s2.contains("alice")).to_equal(true)
```

</details>

#### adding duplicate does not increase length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("a")
expect(s.len()).to_equal(1)
expect(s.contains("a")).to_equal(true)
```

</details>

#### handles two elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("b")
expect(s.contains("a")).to_equal(true)
expect(s.contains("b")).to_equal(true)
expect(s.len()).to_equal(2)
```

</details>

#### handles three elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("b").add("c")
expect(s.contains("a")).to_equal(true)
expect(s.contains("b")).to_equal(true)
expect(s.contains("c")).to_equal(true)
expect(s.len()).to_equal(3)
```

</details>

#### stores integer elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add(1).add(2).add(3)
expect(s.contains(1)).to_equal(true)
expect(s.contains(2)).to_equal(true)
expect(s.contains(3)).to_equal(true)
expect(s.len()).to_equal(3)
```

</details>

#### returns false for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a")
expect(s.contains("b")).to_equal(false)
```

</details>

#### is no longer empty after add

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("x")
expect(s.is_empty()).to_equal(false)
```

</details>

### persistence across multiple adds

#### preserves snapshots

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = PersistentSet.empty()
val s1 = s0.add("a")
val s2 = s1.add("b")
val s3 = s2.add("c")
expect(s0.len()).to_equal(0)
expect(s1.len()).to_equal(1)
expect(s2.len()).to_equal(2)
expect(s3.len()).to_equal(3)
expect(s1.contains("b")).to_equal(false)
expect(s2.contains("c")).to_equal(false)
```

</details>

### remove

#### removes an existing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("b")
val s2 = s.remove("a")
expect(s2.contains("a")).to_equal(false)
expect(s2.contains("b")).to_equal(true)
expect(s2.len()).to_equal(1)
```

</details>

#### does not modify original on remove

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.empty().add("a")
val s2 = s1.remove("a")
expect(s1.contains("a")).to_equal(true)
expect(s1.len()).to_equal(1)
expect(s2.contains("a")).to_equal(false)
expect(s2.len()).to_equal(0)
```

</details>

#### handles removing non-existent element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a")
val s2 = s.remove("b")
expect(s2.len()).to_equal(1)
expect(s2.contains("a")).to_equal(true)
```

</details>

#### removes last element to get empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("only")
val s2 = s.remove("only")
expect(s2.len()).to_equal(0)
expect(s2.is_empty()).to_equal(true)
```

</details>

#### removes from multi-element set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("b").add("c")
val s2 = s.remove("b")
expect(s2.len()).to_equal(2)
expect(s2.contains("a")).to_equal(true)
expect(s2.contains("b")).to_equal(false)
expect(s2.contains("c")).to_equal(true)
```

</details>

#### remove from empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
val s2 = s.remove("nothing")
expect(s2.len()).to_equal(0)
```

</details>

### from_array

#### builds from array of elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b", "c"])
expect(s.len()).to_equal(3)
expect(s.contains("a")).to_equal(true)
expect(s.contains("b")).to_equal(true)
expect(s.contains("c")).to_equal(true)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([])
expect(s.len()).to_equal(0)
expect(s.is_empty()).to_equal(true)
```

</details>

#### handles single element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["only"])
expect(s.contains("only")).to_equal(true)
expect(s.len()).to_equal(1)
```

</details>

#### deduplicates on construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b", "a", "c", "b"])
expect(s.len()).to_equal(3)
```

</details>

### of (alias for from_array)

#### builds set via of

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.of(["x", "y"])
expect(s.len()).to_equal(2)
expect(s.contains("x")).to_equal(true)
expect(s.contains("y")).to_equal(true)
```

</details>

### union

#### merges two disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.from_array(["c", "d"])
val u = s1.union(s2)
expect(u.len()).to_equal(4)
expect(u.contains("a")).to_equal(true)
expect(u.contains("b")).to_equal(true)
expect(u.contains("c")).to_equal(true)
expect(u.contains("d")).to_equal(true)
```

</details>

#### deduplicates overlapping elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "c"])
val s2 = PersistentSet.from_array(["b", "c", "d"])
val u = s1.union(s2)
expect(u.len()).to_equal(4)
```

</details>

#### union with empty returns equivalent set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.empty()
val u = s1.union(s2)
expect(u.len()).to_equal(2)
expect(u.contains("a")).to_equal(true)
```

</details>

#### empty union with other returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.empty()
val s2 = PersistentSet.from_array(["x"])
val u = s1.union(s2)
expect(u.len()).to_equal(1)
expect(u.contains("x")).to_equal(true)
```

</details>

#### does not modify originals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a"])
val s2 = PersistentSet.from_array(["b"])
val u = s1.union(s2)
expect(s1.len()).to_equal(1)
expect(s2.len()).to_equal(1)
expect(u.len()).to_equal(2)
```

</details>

### intersection

#### returns only common elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "c"])
val s2 = PersistentSet.from_array(["b", "c", "d"])
val inter = s1.intersection(s2)
expect(inter.len()).to_equal(2)
expect(inter.contains("b")).to_equal(true)
expect(inter.contains("c")).to_equal(true)
expect(inter.contains("a")).to_equal(false)
expect(inter.contains("d")).to_equal(false)
```

</details>

#### returns empty for disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.from_array(["c", "d"])
val inter = s1.intersection(s2)
expect(inter.len()).to_equal(0)
expect(inter.is_empty()).to_equal(true)
```

</details>

#### intersection with empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.empty()
val inter = s1.intersection(s2)
expect(inter.len()).to_equal(0)
```

</details>

#### intersection with itself returns equivalent set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b", "c"])
val inter = s.intersection(s)
expect(inter.len()).to_equal(3)
```

</details>

### difference

#### returns elements in self but not other

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "c"])
val s2 = PersistentSet.from_array(["b", "d"])
val diff = s1.difference(s2)
expect(diff.len()).to_equal(2)
expect(diff.contains("a")).to_equal(true)
expect(diff.contains("c")).to_equal(true)
expect(diff.contains("b")).to_equal(false)
```

</details>

#### returns empty when self is subset of other

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.from_array(["a", "b", "c"])
val diff = s1.difference(s2)
expect(diff.len()).to_equal(0)
```

</details>

#### difference with empty returns self

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.empty()
val diff = s1.difference(s2)
expect(diff.len()).to_equal(2)
```

</details>

#### difference with itself returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b"])
val diff = s.difference(s)
expect(diff.len()).to_equal(0)
expect(diff.is_empty()).to_equal(true)
```

</details>

### symmetric_difference

#### returns elements in either but not both

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "c"])
val s2 = PersistentSet.from_array(["b", "c", "d"])
val sd = s1.symmetric_difference(s2)
expect(sd.len()).to_equal(2)
expect(sd.contains("a")).to_equal(true)
expect(sd.contains("d")).to_equal(true)
expect(sd.contains("b")).to_equal(false)
expect(sd.contains("c")).to_equal(false)
```

</details>

#### symmetric difference of identical sets is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b"])
val sd = s.symmetric_difference(s)
expect(sd.len()).to_equal(0)
```

</details>

#### symmetric difference of disjoint sets is union

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a"])
val s2 = PersistentSet.from_array(["b"])
val sd = s1.symmetric_difference(s2)
expect(sd.len()).to_equal(2)
expect(sd.contains("a")).to_equal(true)
expect(sd.contains("b")).to_equal(true)
```

</details>

### is_subset

#### returns true when self is subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.from_array(["a", "b", "c"])
expect(s1.is_subset(s2)).to_equal(true)
```

</details>

#### returns false when not subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "x"])
val s2 = PersistentSet.from_array(["a", "b", "c"])
expect(s1.is_subset(s2)).to_equal(false)
```

</details>

#### empty set is subset of any set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.empty()
val s2 = PersistentSet.from_array(["a"])
expect(s1.is_subset(s2)).to_equal(true)
```

</details>

#### set is subset of itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b"])
expect(s.is_subset(s)).to_equal(true)
```

</details>

### is_superset

#### returns true when self is superset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b", "c"])
val s2 = PersistentSet.from_array(["a", "b"])
expect(s1.is_superset(s2)).to_equal(true)
```

</details>

#### returns false when not superset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a", "b"])
val s2 = PersistentSet.from_array(["a", "b", "c"])
expect(s1.is_superset(s2)).to_equal(false)
```

</details>

#### any set is superset of empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = PersistentSet.from_array(["a"])
val s2 = PersistentSet.empty()
expect(s1.is_superset(s2)).to_equal(true)
```

</details>

### filter

#### keeps elements matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2, 3, 4, 5])
val evens = s.filter(fn(x): x % 2 == 0)
expect(evens.len()).to_equal(2)
expect(evens.contains(2)).to_equal(true)
expect(evens.contains(4)).to_equal(true)
expect(evens.contains(1)).to_equal(false)
```

</details>

#### returns empty when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2, 3])
val filtered = s.filter(fn(x): x > 100)
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
val s = PersistentSet.from_array([1, 2, 3])
val filtered = s.filter(fn(x): x > 0)
expect(filtered.len()).to_equal(3)
```

</details>

### map

#### transforms all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2, 3])
val doubled = s.map(fn(x): x * 2)
expect(doubled.len()).to_equal(3)
expect(doubled.contains(2)).to_equal(true)
expect(doubled.contains(4)).to_equal(true)
expect(doubled.contains(6)).to_equal(true)
```

</details>

#### deduplicates mapped results

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2, 3, 4])
val modded = s.map(fn(x): x % 2)
expect(modded.len()).to_equal(2)
expect(modded.contains(0)).to_equal(true)
expect(modded.contains(1)).to_equal(true)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2])
val mapped = s.map(fn(x): x + 10)
expect(s.len()).to_equal(2)
expect(s.contains(1)).to_equal(true)
expect(mapped.contains(1)).to_equal(false)
```

</details>

### fold

#### sums all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array([1, 2, 3])
val total = s.fold(0, fn(acc, x): acc + x)
expect(total).to_equal(6)
```

</details>

#### fold over empty returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty()
val result = s.fold(42, fn(acc, x): acc + x)
expect(result).to_equal(42)
```

</details>

### to_array

#### returns correct number of elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["x", "y", "z"])
val arr = s.to_array()
expect(arr.len()).to_equal(3)
```

</details>

#### single element set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["only"])
val arr = s.to_array()
expect(arr.len()).to_equal(1)
```

</details>

### copy

#### returns identical set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.from_array(["a", "b"])
val c = s.copy()
expect(c.contains("a")).to_equal(true)
expect(c.contains("b")).to_equal(true)
expect(c.len()).to_equal(2)
```

</details>

### stress test

#### handles many elements via helper fn

1. fn run stress
2. var s = PersistentSet empty
3. s = s add
4. s len
   - Expected: run_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_stress() -> i64:
    var s = PersistentSet.empty()
    var i = 0
    while i < 100:
        s = s.add("item_{i}")
        i = i + 1
    s.len()
expect(run_stress()).to_equal(100)
```

</details>

#### add and check many elements

1. fn run check stress
2. var s = PersistentSet empty
3. s = s add
   - Expected: run_check_stress() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_check_stress() -> i64:
    var s = PersistentSet.empty()
    var i = 0
    while i < 50:
        s = s.add("k_{i}")
        i = i + 1
    var ok_count = 0
    i = 0
    while i < 50:
        if s.contains("k_{i}"):
            ok_count = ok_count + 1
        i = i + 1
    ok_count
expect(run_check_stress()).to_equal(50)
```

</details>

#### remove many elements

1. fn run remove stress
2. var s = PersistentSet empty
3. s = s add
4. s = s remove
5. s len
   - Expected: run_remove_stress() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_remove_stress() -> i64:
    var s = PersistentSet.empty()
    var i = 0
    while i < 30:
        s = s.add("r_{i}")
        i = i + 1
    i = 0
    while i < 15:
        s = s.remove("r_{i}")
        i = i + 1
    s.len()
expect(run_remove_stress()).to_equal(15)
```

</details>

### edge cases

#### add same element repeatedly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("a").add("a").add("a")
expect(s.len()).to_equal(1)
```

</details>

#### empty string as element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("")
expect(s.contains("")).to_equal(true)
expect(s.len()).to_equal(1)
```

</details>

#### add and remove same element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = PersistentSet.empty().add("temp").remove("temp")
expect(s.len()).to_equal(0)
expect(s.is_empty()).to_equal(true)
expect(s.contains("temp")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/persistent_set_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentSet
- empty set
- add and contains
- persistence across multiple adds
- remove
- from_array
- of (alias for from_array)
- union
- intersection
- difference
- symmetric_difference
- is_subset
- is_superset
- filter
- map
- fold
- to_array
- copy
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
