# Concurrent Providers Specification

> 1. expect   rt hashmap len

<!-- sdn-diagram:id=concurrent_providers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_providers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_providers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_providers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 90 | 90 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Providers Specification

## Scenarios

### Concurrent Providers

### HashMap

#### creates a new empty hashmap

1. expect   rt hashmap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
expect __rt_hashmap_len(h) == 0
```

</details>

#### inserts and retrieves a value

1.   rt hashmap insert
2. expect   rt hashmap get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "key1", 42)
expect __rt_hashmap_get(h, "key1") == 42
```

</details>

#### returns nil for missing key

1. expect   rt hashmap get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
expect __rt_hashmap_get(h, "nope") == nil
```

</details>

#### reports contains_key correctly

1.   rt hashmap insert
2. expect   rt hashmap contains key
3. expect   rt hashmap contains key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "x", 1)
expect __rt_hashmap_contains_key(h, "x") == true
expect __rt_hashmap_contains_key(h, "y") == false
```

</details>

#### removes a key

1.   rt hashmap insert
2. expect   rt hashmap contains key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "rm", 99)
val removed = __rt_hashmap_remove(h, "rm")
expect removed == 99
expect __rt_hashmap_contains_key(h, "rm") == false
```

</details>

#### removes missing key returns nil

1. expect   rt hashmap remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
expect __rt_hashmap_remove(h, "missing") == nil
```

</details>

#### tracks length correctly

1.   rt hashmap insert
2.   rt hashmap insert
3.   rt hashmap insert
4. expect   rt hashmap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "a", 1)
__rt_hashmap_insert(h, "b", 2)
__rt_hashmap_insert(h, "c", 3)
expect __rt_hashmap_len(h) == 3
```

</details>

#### clears all entries

1.   rt hashmap insert
2.   rt hashmap insert
3.   rt hashmap clear
4. expect   rt hashmap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "a", 1)
__rt_hashmap_insert(h, "b", 2)
__rt_hashmap_clear(h)
expect __rt_hashmap_len(h) == 0
```

</details>

#### returns keys as array

1.   rt hashmap insert
2.   rt hashmap insert
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "alpha", 1)
__rt_hashmap_insert(h, "beta", 2)
val keys = __rt_hashmap_keys(h)
expect len(keys) == 2
```

</details>

#### returns values as array

1.   rt hashmap insert
2.   rt hashmap insert
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "x", 10)
__rt_hashmap_insert(h, "y", 20)
val vals = __rt_hashmap_values(h)
expect len(vals) == 2
```

</details>

#### returns entries as array of pairs

1.   rt hashmap insert
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "k", 99)
val entries = __rt_hashmap_entries(h)
expect len(entries) == 1
```

</details>

#### overwrites existing key

1.   rt hashmap insert
2.   rt hashmap insert
3. expect   rt hashmap get
4. expect   rt hashmap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "dup", 1)
__rt_hashmap_insert(h, "dup", 2)
expect __rt_hashmap_get(h, "dup") == 2
expect __rt_hashmap_len(h) == 1
```

</details>

#### stores string values

1.   rt hashmap insert
2. expect   rt hashmap get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "greeting", "hello")
expect __rt_hashmap_get(h, "greeting") == "hello"
```

</details>

<details>
<summary>Advanced: handles stress with 100+ items</summary>

#### handles stress with 100+ items

1.   rt hashmap insert
2. expect   rt hashmap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
var i = 0
while i < 100:
    __rt_hashmap_insert(h, "key_{i}", i)
    i = i + 1
expect __rt_hashmap_len(h) == 100
```

</details>


</details>

#### insert returns true for new key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
val result = __rt_hashmap_insert(h, "new", 1)
expect result == true
```

</details>

#### insert returns false for existing key

1.   rt hashmap insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "dup", 1)
val result = __rt_hashmap_insert(h, "dup", 2)
expect result == false
```

</details>

### HashSet

#### creates a new empty hashset

1. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
expect __rt_hashset_len(s) == 0
```

</details>

#### inserts and checks membership

1.   rt hashset insert
2. expect   rt hashset contains
3. expect   rt hashset contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
__rt_hashset_insert(s, "apple")
expect __rt_hashset_contains(s, "apple") == true
expect __rt_hashset_contains(s, "banana") == false
```

</details>

#### removes a value

1.   rt hashset insert
2. expect   rt hashset remove
3. expect   rt hashset contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
__rt_hashset_insert(s, "x")
expect __rt_hashset_remove(s, "x") == true
expect __rt_hashset_contains(s, "x") == false
```

</details>

#### remove returns false for missing

1. expect   rt hashset remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
expect __rt_hashset_remove(s, "nope") == false
```

</details>

#### tracks length

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
__rt_hashset_insert(s, "a")
__rt_hashset_insert(s, "b")
__rt_hashset_insert(s, "c")
expect __rt_hashset_len(s) == 3
```

</details>

#### clears all elements

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset clear
4. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
__rt_hashset_insert(s, "x")
__rt_hashset_insert(s, "y")
__rt_hashset_clear(s)
expect __rt_hashset_len(s) == 0
```

</details>

#### converts to array

1.   rt hashset insert
2.   rt hashset insert
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_hashset_new()
__rt_hashset_insert(s, "one")
__rt_hashset_insert(s, "two")
val arr = __rt_hashset_to_array(s)
expect len(arr) == 2
```

</details>

#### computes union

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4.   rt hashset insert
5. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
__rt_hashset_insert(a, "2")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "2")
__rt_hashset_insert(b, "3")
val u = __rt_hashset_union(a, b)
expect __rt_hashset_len(u) == 3
```

</details>

#### computes intersection

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4.   rt hashset insert
5. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
__rt_hashset_insert(a, "2")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "2")
__rt_hashset_insert(b, "3")
val inter = __rt_hashset_intersection(a, b)
expect __rt_hashset_len(inter) == 1
```

</details>

#### computes difference

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4. expect   rt hashset len
5. expect   rt hashset contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
__rt_hashset_insert(a, "2")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "2")
val d = __rt_hashset_difference(a, b)
expect __rt_hashset_len(d) == 1
expect __rt_hashset_contains(d, "1") == true
```

</details>

#### computes symmetric difference

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4.   rt hashset insert
5. expect   rt hashset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
__rt_hashset_insert(a, "2")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "2")
__rt_hashset_insert(b, "3")
val sd = __rt_hashset_symmetric_difference(a, b)
expect __rt_hashset_len(sd) == 2
```

</details>

#### checks subset

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4. expect   rt hashset is subset
5. expect   rt hashset is subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "1")
__rt_hashset_insert(b, "2")
expect __rt_hashset_is_subset(a, b) == true
expect __rt_hashset_is_subset(b, a) == false
```

</details>

#### checks superset

1.   rt hashset insert
2.   rt hashset insert
3.   rt hashset insert
4. expect   rt hashset is superset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_hashset_new()
__rt_hashset_insert(a, "1")
__rt_hashset_insert(a, "2")
val b = __rt_hashset_new()
__rt_hashset_insert(b, "1")
expect __rt_hashset_is_superset(a, b) == true
```

</details>

### BTreeMap

#### creates a new empty btreemap

1. expect   rt btreemap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
expect __rt_btreemap_len(m) == 0
```

</details>

#### inserts and retrieves

1.   rt btreemap insert
2. expect   rt btreemap get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "key", 42)
expect __rt_btreemap_get(m, "key") == 42
```

</details>

#### returns nil for missing key

1. expect   rt btreemap get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
expect __rt_btreemap_get(m, "nope") == nil
```

</details>

#### contains_key works

1.   rt btreemap insert
2. expect   rt btreemap contains key
3. expect   rt btreemap contains key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "x", 1)
expect __rt_btreemap_contains_key(m, "x") == true
expect __rt_btreemap_contains_key(m, "y") == false
```

</details>

#### removes a key

1.   rt btreemap insert
2. expect   rt btreemap remove
3. expect   rt btreemap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "rm", 5)
expect __rt_btreemap_remove(m, "rm") == 5
expect __rt_btreemap_len(m) == 0
```

</details>

#### tracks length

1.   rt btreemap insert
2.   rt btreemap insert
3. expect   rt btreemap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_insert(m, "b", 2)
expect __rt_btreemap_len(m) == 2
```

</details>

#### clears all entries

1.   rt btreemap insert
2.   rt btreemap clear
3. expect   rt btreemap len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_clear(m)
expect __rt_btreemap_len(m) == 0
```

</details>

#### returns sorted keys

1.   rt btreemap insert
2.   rt btreemap insert
3.   rt btreemap insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "c", 3)
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_insert(m, "b", 2)
val keys = __rt_btreemap_keys(m)
expect keys[0] == "a"
expect keys[1] == "b"
expect keys[2] == "c"
```

</details>

#### returns values in key order

1.   rt btreemap insert
2.   rt btreemap insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "b", 20)
__rt_btreemap_insert(m, "a", 10)
val vals = __rt_btreemap_values(m)
expect vals[0] == 10
expect vals[1] == 20
```

</details>

#### returns entries in key order

1.   rt btreemap insert
2.   rt btreemap insert
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "b", 2)
__rt_btreemap_insert(m, "a", 1)
val entries = __rt_btreemap_entries(m)
expect len(entries) == 2
```

</details>

#### gets first key (smallest)

1.   rt btreemap insert
2.   rt btreemap insert
3. expect   rt btreemap first key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "z", 26)
__rt_btreemap_insert(m, "a", 1)
expect __rt_btreemap_first_key(m) == "a"
```

</details>

#### gets last key (largest)

1.   rt btreemap insert
2.   rt btreemap insert
3. expect   rt btreemap last key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_insert(m, "z", 26)
expect __rt_btreemap_last_key(m) == "z"
```

</details>

#### first_key returns nil for empty map

1. expect   rt btreemap first key


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = __rt_btreemap_new()
expect __rt_btreemap_first_key(m) == nil
```

</details>

### BTreeSet

#### creates a new empty btreeset

1. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
expect __rt_btreeset_len(s) == 0
```

</details>

#### inserts and checks membership

1.   rt btreeset insert
2. expect   rt btreeset contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "apple")
expect __rt_btreeset_contains(s, "apple") == true
```

</details>

#### removes a value

1.   rt btreeset insert
2. expect   rt btreeset remove
3. expect   rt btreeset contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "x")
expect __rt_btreeset_remove(s, "x") == true
expect __rt_btreeset_contains(s, "x") == false
```

</details>

#### tracks length

1.   rt btreeset insert
2.   rt btreeset insert
3. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "a")
__rt_btreeset_insert(s, "b")
expect __rt_btreeset_len(s) == 2
```

</details>

#### clears all elements

1.   rt btreeset insert
2.   rt btreeset clear
3. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "x")
__rt_btreeset_clear(s)
expect __rt_btreeset_len(s) == 0
```

</details>

#### converts to sorted array

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "c")
__rt_btreeset_insert(s, "a")
__rt_btreeset_insert(s, "b")
val arr = __rt_btreeset_to_array(s)
expect arr[0] == "a"
expect arr[1] == "b"
expect arr[2] == "c"
```

</details>

#### gets first element

1.   rt btreeset insert
2.   rt btreeset insert
3. expect   rt btreeset first


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "z")
__rt_btreeset_insert(s, "a")
expect __rt_btreeset_first(s) == "a"
```

</details>

#### gets last element

1.   rt btreeset insert
2.   rt btreeset insert
3. expect   rt btreeset last


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "a")
__rt_btreeset_insert(s, "z")
expect __rt_btreeset_last(s) == "z"
```

</details>

#### computes union

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4.   rt btreeset insert
5. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
__rt_btreeset_insert(a, "2")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "2")
__rt_btreeset_insert(b, "3")
val u = __rt_btreeset_union(a, b)
expect __rt_btreeset_len(u) == 3
```

</details>

#### computes intersection

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4.   rt btreeset insert
5. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
__rt_btreeset_insert(a, "2")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "2")
__rt_btreeset_insert(b, "3")
val inter = __rt_btreeset_intersection(a, b)
expect __rt_btreeset_len(inter) == 1
```

</details>

#### computes difference

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
__rt_btreeset_insert(a, "2")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "2")
val d = __rt_btreeset_difference(a, b)
expect __rt_btreeset_len(d) == 1
```

</details>

#### computes symmetric difference

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4.   rt btreeset insert
5. expect   rt btreeset len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
__rt_btreeset_insert(a, "2")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "2")
__rt_btreeset_insert(b, "3")
val sd = __rt_btreeset_symmetric_difference(a, b)
expect __rt_btreeset_len(sd) == 2
```

</details>

#### checks subset

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4. expect   rt btreeset is subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "1")
__rt_btreeset_insert(b, "2")
expect __rt_btreeset_is_subset(a, b) == true
```

</details>

#### checks superset

1.   rt btreeset insert
2.   rt btreeset insert
3.   rt btreeset insert
4. expect   rt btreeset is superset


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
__rt_btreeset_insert(a, "2")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "1")
expect __rt_btreeset_is_superset(a, b) == true
```

</details>

### Channel

#### creates a channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
expect ch >= 1
```

</details>

#### sends and receives a value

1. rt channel send
2. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, 42)
expect rt_channel_try_recv(ch) == 42
```

</details>

#### try_recv returns nil on empty

1. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
expect rt_channel_try_recv(ch) == nil
```

</details>

#### preserves FIFO order

1. rt channel send
2. rt channel send
3. rt channel send
4. expect rt channel try recv
5. expect rt channel try recv
6. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, 1)
rt_channel_send(ch, 2)
rt_channel_send(ch, 3)
expect rt_channel_try_recv(ch) == 1
expect rt_channel_try_recv(ch) == 2
expect rt_channel_try_recv(ch) == 3
```

</details>

#### closes a channel

1. rt channel close
2. expect rt channel is closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_close(ch)
expect rt_channel_is_closed(ch) == 1
```

</details>

#### is_closed returns 0 for open channel

1. expect rt channel is closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
expect rt_channel_is_closed(ch) == 0
```

</details>

#### sends and receives string values

1. rt channel send
2. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, "hello")
expect rt_channel_try_recv(ch) == "hello"
```

</details>

#### sends and receives boolean values

1. rt channel send
2. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, true)
expect rt_channel_try_recv(ch) == true
```

</details>

#### sends multiple types

1. rt channel send
2. rt channel send
3. rt channel send
4. expect rt channel try recv
5. expect rt channel try recv
6. expect rt channel try recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, 42)
rt_channel_send(ch, "text")
rt_channel_send(ch, true)
expect rt_channel_try_recv(ch) == 42
expect rt_channel_try_recv(ch) == "text"
expect rt_channel_try_recv(ch) == true
```

</details>

#### blocking recv works after send

1. rt channel send
2. expect rt channel recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
rt_channel_send(ch, 99)
expect rt_channel_recv(ch) == 99
```

</details>

### Thread

#### reports parallelism >= 1

1. expect rt thread available parallelism


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect rt_thread_available_parallelism() >= 1
```

</details>

#### sleep does not error

1. rt thread sleep


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_sleep(1)
expect true
```

</details>

#### yield does not error

1. rt thread yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_yield()
expect true
```

</details>

#### spawn returns valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated_with_args(\x, y: nil, 1, 2)
expect handle >= 1
```

</details>

#### join returns result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated_with_args(\x, y: nil, 1, 2)
val result = rt_thread_join(handle)
# synchronous execution returns nil for stub closure
expect result == nil
```

</details>

#### spawn with channel communication

1. rt channel send
2. rt thread join


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
val handle = rt_thread_spawn_isolated_with_args(\data, channel_id:
    rt_channel_send(channel_id, data)
    return nil
, 42, ch)
val result = rt_channel_recv(ch)
rt_thread_join(handle)
expect result == 42
```

</details>

#### spawn with computation

1. rt channel send
2. rt thread join


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
val handle = rt_thread_spawn_isolated_with_args(\a, b:
    rt_channel_send(b, a * 2)
    return nil
, 21, ch)
val result = rt_channel_recv(ch)
rt_thread_join(handle)
expect result == 42
```

</details>

#### multiple spawns

1. rt channel send
2. rt channel send
3. rt thread join
4. rt thread join


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = rt_channel_new()
val h1 = rt_thread_spawn_isolated_with_args(\d, c:
    rt_channel_send(c, d)
    return nil
, 10, ch)
val h2 = rt_thread_spawn_isolated_with_args(\d, c:
    rt_channel_send(c, d)
    return nil
, 20, ch)
val r1 = rt_channel_recv(ch)
val r2 = rt_channel_recv(ch)
rt_thread_join(h1)
rt_thread_join(h2)
expect r1 + r2 == 30
```

</details>

### Mutex

#### creates a mutex with initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(42)
expect m != nil
```

</details>

#### locks and reads value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(42)
val v = rt_mutex_lock(m)
expect v != nil
```

</details>

#### try_lock succeeds when unlocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(10)
val v = rt_mutex_try_lock(m)
expect v != nil
```

</details>

#### unlock stores new value

1. rt mutex lock
2. rt mutex unlock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(1)
rt_mutex_lock(m)
rt_mutex_unlock(m, 2)
val v = rt_mutex_lock(m)
expect v != nil
```

</details>

#### multiple lock/unlock cycles

1. rt mutex lock
2. rt mutex unlock
3. rt mutex lock
4. rt mutex unlock
5. rt mutex lock
6. rt mutex unlock


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(0)
rt_mutex_lock(m)
rt_mutex_unlock(m, 1)
rt_mutex_lock(m)
rt_mutex_unlock(m, 2)
rt_mutex_lock(m)
rt_mutex_unlock(m, 3)
expect true
```

</details>

#### creates with string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(100)
expect m != nil
```

</details>

#### creates multiple mutexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1 = rt_mutex_new(1)
val m2 = rt_mutex_new(2)
val m3 = rt_mutex_new(3)
expect m1 != nil
expect m2 != nil
expect m3 != nil
```

</details>

#### lock returns a value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(99)
val locked = rt_mutex_lock(m)
# locked is the protected value (may be raw runtime representation)
expect locked != nil
```

</details>

### RwLock

#### creates a rwlock with initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(42)
expect rw != nil
```

</details>

#### read lock returns value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(42)
val v = rt_rwlock_read(rw)
expect v != nil
```

</details>

#### write lock returns value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(42)
val v = rt_rwlock_write(rw)
expect v != nil
```

</details>

#### try_read succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(10)
val v = rt_rwlock_try_read(rw)
expect v != nil
```

</details>

#### try_write succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(10)
val v = rt_rwlock_try_write(rw)
expect v != nil
```

</details>

#### set updates value

1. rt rwlock set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(1)
rt_rwlock_set(rw, 2)
expect true
```

</details>

#### creates multiple rwlocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = rt_rwlock_new(1)
val r2 = rt_rwlock_new(2)
expect r1 != nil
expect r2 != nil
```

</details>

#### read after set

1. rt rwlock set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(10)
rt_rwlock_set(rw, 20)
val v = rt_rwlock_read(rw)
expect v != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Concurrent Providers
- HashMap
- HashSet
- BTreeMap
- BTreeSet
- Channel
- Thread
- Mutex
- RwLock

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 90 |
| Active scenarios | 90 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
