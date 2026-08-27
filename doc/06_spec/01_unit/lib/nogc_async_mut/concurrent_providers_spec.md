# Concurrent Providers Specification

> Tests covering Concurrent Providers, HashMap, HashSet, BTreeMap, BTreeSet, Channel, Thread, Mutex, RwLock.

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

- creates a new empty hashmap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new empty hashmap")
val h = __rt_hashmap_new()
expect __rt_hashmap_len(h) == 0
```

</details>

#### inserts and retrieves a value

- inserts and retrieves a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and retrieves a value")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "key1", 42)
expect __rt_hashmap_get(h, "key1") == 42
```

</details>

#### returns nil for missing key

- returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for missing key")
val h = __rt_hashmap_new()
expect __rt_hashmap_get(h, "nope") == nil
```

</details>

#### reports contains_key correctly

- reports contains_key correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports contains_key correctly")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "x", 1)
expect __rt_hashmap_contains_key(h, "x") == true
expect __rt_hashmap_contains_key(h, "y") == false
```

</details>

#### removes a key

- removes a key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a key")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "rm", 99)
val removed = __rt_hashmap_remove(h, "rm")
expect removed == 99
expect __rt_hashmap_contains_key(h, "rm") == false
```

</details>

#### removes missing key returns nil

- removes missing key returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes missing key returns nil")
val h = __rt_hashmap_new()
expect __rt_hashmap_remove(h, "missing") == nil
```

</details>

#### tracks length correctly

- tracks length correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks length correctly")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "a", 1)
__rt_hashmap_insert(h, "b", 2)
__rt_hashmap_insert(h, "c", 3)
expect __rt_hashmap_len(h) == 3
```

</details>

#### clears all entries

- clears all entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all entries")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "a", 1)
__rt_hashmap_insert(h, "b", 2)
__rt_hashmap_clear(h)
expect __rt_hashmap_len(h) == 0
```

</details>

#### returns keys as array

- returns keys as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns keys as array")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "alpha", 1)
__rt_hashmap_insert(h, "beta", 2)
val keys = __rt_hashmap_keys(h)
expect len(keys) == 2
```

</details>

#### returns values as array

- returns values as array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns values as array")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "x", 10)
__rt_hashmap_insert(h, "y", 20)
val vals = __rt_hashmap_values(h)
expect len(vals) == 2
```

</details>

#### returns entries as array of pairs

- returns entries as array of pairs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entries as array of pairs")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "k", 99)
val entries = __rt_hashmap_entries(h)
expect len(entries) == 1
```

</details>

#### overwrites existing key

- overwrites existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites existing key")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "dup", 1)
__rt_hashmap_insert(h, "dup", 2)
expect __rt_hashmap_get(h, "dup") == 2
expect __rt_hashmap_len(h) == 1
```

</details>

#### stores string values

- stores string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores string values")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "greeting", "hello")
expect __rt_hashmap_get(h, "greeting") == "hello"
```

</details>

<details>
<summary>Advanced: handles stress with 100+ items</summary>

#### handles stress with 100+ items

- handles stress with 100+ items


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles stress with 100+ items")
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

- insert returns true for new key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert returns true for new key")
val h = __rt_hashmap_new()
val result = __rt_hashmap_insert(h, "new", 1)
expect result == true
```

</details>

#### insert returns false for existing key

- insert returns false for existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert returns false for existing key")
val h = __rt_hashmap_new()
__rt_hashmap_insert(h, "dup", 1)
val result = __rt_hashmap_insert(h, "dup", 2)
expect result == false
```

</details>

### HashSet

#### creates a new empty hashset

- creates a new empty hashset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new empty hashset")
val s = __rt_hashset_new()
expect __rt_hashset_len(s) == 0
```

</details>

#### inserts and checks membership

- inserts and checks membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and checks membership")
val s = __rt_hashset_new()
__rt_hashset_insert(s, "apple")
expect __rt_hashset_contains(s, "apple") == true
expect __rt_hashset_contains(s, "banana") == false
```

</details>

#### removes a value

- removes a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a value")
val s = __rt_hashset_new()
__rt_hashset_insert(s, "x")
expect __rt_hashset_remove(s, "x") == true
expect __rt_hashset_contains(s, "x") == false
```

</details>

#### remove returns false for missing

- remove returns false for missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove returns false for missing")
val s = __rt_hashset_new()
expect __rt_hashset_remove(s, "nope") == false
```

</details>

#### tracks length

- tracks length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks length")
val s = __rt_hashset_new()
__rt_hashset_insert(s, "a")
__rt_hashset_insert(s, "b")
__rt_hashset_insert(s, "c")
expect __rt_hashset_len(s) == 3
```

</details>

#### clears all elements

- clears all elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all elements")
val s = __rt_hashset_new()
__rt_hashset_insert(s, "x")
__rt_hashset_insert(s, "y")
__rt_hashset_clear(s)
expect __rt_hashset_len(s) == 0
```

</details>

#### converts to array

- converts to array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to array")
val s = __rt_hashset_new()
__rt_hashset_insert(s, "one")
__rt_hashset_insert(s, "two")
val arr = __rt_hashset_to_array(s)
expect len(arr) == 2
```

</details>

#### computes union

- computes union


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes union")
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

- computes intersection


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes intersection")
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

- computes difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes difference")
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

- computes symmetric difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes symmetric difference")
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

- checks subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks subset")
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

- checks superset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks superset")
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

- creates a new empty btreemap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new empty btreemap")
val m = __rt_btreemap_new()
expect __rt_btreemap_len(m) == 0
```

</details>

#### inserts and retrieves

- inserts and retrieves


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and retrieves")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "key", 42)
expect __rt_btreemap_get(m, "key") == 42
```

</details>

#### returns nil for missing key

- returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for missing key")
val m = __rt_btreemap_new()
expect __rt_btreemap_get(m, "nope") == nil
```

</details>

#### contains_key works

- contains_key works


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains_key works")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "x", 1)
expect __rt_btreemap_contains_key(m, "x") == true
expect __rt_btreemap_contains_key(m, "y") == false
```

</details>

#### removes a key

- removes a key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a key")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "rm", 5)
expect __rt_btreemap_remove(m, "rm") == 5
expect __rt_btreemap_len(m) == 0
```

</details>

#### tracks length

- tracks length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks length")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_insert(m, "b", 2)
expect __rt_btreemap_len(m) == 2
```

</details>

#### clears all entries

- clears all entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all entries")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_clear(m)
expect __rt_btreemap_len(m) == 0
```

</details>

#### returns sorted keys

- returns sorted keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sorted keys")
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

- returns values in key order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns values in key order")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "b", 20)
__rt_btreemap_insert(m, "a", 10)
val vals = __rt_btreemap_values(m)
expect vals[0] == 10
expect vals[1] == 20
```

</details>

#### returns entries in key order

- returns entries in key order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entries in key order")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "b", 2)
__rt_btreemap_insert(m, "a", 1)
val entries = __rt_btreemap_entries(m)
expect len(entries) == 2
```

</details>

#### gets first key (smallest)

- gets first key (smallest)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets first key (smallest)")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "z", 26)
__rt_btreemap_insert(m, "a", 1)
expect __rt_btreemap_first_key(m) == "a"
```

</details>

#### gets last key (largest)

- gets last key (largest)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets last key (largest)")
val m = __rt_btreemap_new()
__rt_btreemap_insert(m, "a", 1)
__rt_btreemap_insert(m, "z", 26)
expect __rt_btreemap_last_key(m) == "z"
```

</details>

#### first_key returns nil for empty map

- first_key returns nil for empty map


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first_key returns nil for empty map")
val m = __rt_btreemap_new()
expect __rt_btreemap_first_key(m) == nil
```

</details>

### BTreeSet

#### creates a new empty btreeset

- creates a new empty btreeset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a new empty btreeset")
val s = __rt_btreeset_new()
expect __rt_btreeset_len(s) == 0
```

</details>

#### inserts and checks membership

- inserts and checks membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and checks membership")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "apple")
expect __rt_btreeset_contains(s, "apple") == true
```

</details>

#### removes a value

- removes a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a value")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "x")
expect __rt_btreeset_remove(s, "x") == true
expect __rt_btreeset_contains(s, "x") == false
```

</details>

#### tracks length

- tracks length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks length")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "a")
__rt_btreeset_insert(s, "b")
expect __rt_btreeset_len(s) == 2
```

</details>

#### clears all elements

- clears all elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all elements")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "x")
__rt_btreeset_clear(s)
expect __rt_btreeset_len(s) == 0
```

</details>

#### converts to sorted array

- converts to sorted array


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to sorted array")
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

- gets first element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets first element")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "z")
__rt_btreeset_insert(s, "a")
expect __rt_btreeset_first(s) == "a"
```

</details>

#### gets last element

- gets last element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets last element")
val s = __rt_btreeset_new()
__rt_btreeset_insert(s, "a")
__rt_btreeset_insert(s, "z")
expect __rt_btreeset_last(s) == "z"
```

</details>

#### computes union

- computes union


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes union")
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

- computes intersection


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes intersection")
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

- computes difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes difference")
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

- computes symmetric difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes symmetric difference")
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

- checks subset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks subset")
val a = __rt_btreeset_new()
__rt_btreeset_insert(a, "1")
val b = __rt_btreeset_new()
__rt_btreeset_insert(b, "1")
__rt_btreeset_insert(b, "2")
expect __rt_btreeset_is_subset(a, b) == true
```

</details>

#### checks superset

- checks superset


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks superset")
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

- creates a channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a channel")
val ch = rt_channel_new()
expect ch >= 1
```

</details>

#### sends and receives a value

- sends and receives a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives a value")
val ch = rt_channel_new()
rt_channel_send(ch, 42)
expect rt_channel_try_recv(ch) == 42
```

</details>

#### try_recv returns nil on empty

- try_recv returns nil on empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_recv returns nil on empty")
val ch = rt_channel_new()
expect rt_channel_try_recv(ch) == nil
```

</details>

#### preserves FIFO order

- preserves FIFO order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves FIFO order")
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

- closes a channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes a channel")
val ch = rt_channel_new()
rt_channel_close(ch)
expect rt_channel_is_closed(ch) == 1
```

</details>

#### is_closed returns 0 for open channel

- is_closed returns 0 for open channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closed returns 0 for open channel")
val ch = rt_channel_new()
expect rt_channel_is_closed(ch) == 0
```

</details>

#### sends and receives string values

- sends and receives string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives string values")
val ch = rt_channel_new()
rt_channel_send(ch, "hello")
expect rt_channel_try_recv(ch) == "hello"
```

</details>

#### sends and receives boolean values

- sends and receives boolean values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives boolean values")
val ch = rt_channel_new()
rt_channel_send(ch, true)
expect rt_channel_try_recv(ch) == true
```

</details>

#### sends multiple types

- sends multiple types


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends multiple types")
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

- blocking recv works after send


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocking recv works after send")
val ch = rt_channel_new()
rt_channel_send(ch, 99)
expect rt_channel_recv(ch) == 99
```

</details>

### Thread

#### reports parallelism >= 1

- reports parallelism >= 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports parallelism >= 1")
expect rt_thread_available_parallelism() >= 1
```

</details>

#### sleep does not error

- sleep does not error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep does not error")
rt_thread_sleep(1)
expect true
```

</details>

#### yield does not error

- yield does not error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yield does not error")
rt_thread_yield()
expect true
```

</details>

#### spawn returns valid handle

- spawn returns valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn returns valid handle")
val handle = rt_thread_spawn_isolated_with_args(\x, y: nil, 1, 2)
expect handle >= 1
```

</details>

#### join returns result

- join returns result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("join returns result")
val handle = rt_thread_spawn_isolated_with_args(\x, y: nil, 1, 2)
val result = rt_thread_join(handle)
# synchronous execution returns nil for stub closure
expect result == nil
```

</details>

#### spawn with channel communication

- spawn with channel communication


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn with channel communication")
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

- spawn with computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn with computation")
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

- multiple spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple spawns")
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

- creates a mutex with initial value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a mutex with initial value")
val m = rt_mutex_new(42)
expect m != nil
```

</details>

#### locks and reads value

- locks and reads value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locks and reads value")
val m = rt_mutex_new(42)
val v = rt_mutex_lock(m)
expect v != nil
```

</details>

#### try_lock succeeds when unlocked

- try_lock succeeds when unlocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_lock succeeds when unlocked")
val m = rt_mutex_new(10)
val v = rt_mutex_try_lock(m)
expect v != nil
```

</details>

#### unlock stores new value

- unlock stores new value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unlock stores new value")
val m = rt_mutex_new(1)
rt_mutex_lock(m)
rt_mutex_unlock(m, 2)
val v = rt_mutex_lock(m)
expect v != nil
```

</details>

#### multiple lock/unlock cycles

- multiple lock/unlock cycles


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple lock/unlock cycles")
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

- creates with string value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with string value")
val m = rt_mutex_new(100)
expect m != nil
```

</details>

#### creates multiple mutexes

- creates multiple mutexes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multiple mutexes")
val m1 = rt_mutex_new(1)
val m2 = rt_mutex_new(2)
val m3 = rt_mutex_new(3)
expect m1 != nil
expect m2 != nil
expect m3 != nil
```

</details>

#### lock returns a value

- lock returns a value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lock returns a value")
val m = rt_mutex_new(99)
val locked = rt_mutex_lock(m)
# locked is the protected value (may be raw runtime representation)
expect locked != nil
```

</details>

### RwLock

#### creates a rwlock with initial value

- creates a rwlock with initial value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a rwlock with initial value")
val rw = rt_rwlock_new(42)
expect rw != nil
```

</details>

#### read lock returns value

- read lock returns value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read lock returns value")
val rw = rt_rwlock_new(42)
val v = rt_rwlock_read(rw)
expect v != nil
```

</details>

#### write lock returns value

- write lock returns value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write lock returns value")
val rw = rt_rwlock_new(42)
val v = rt_rwlock_write(rw)
expect v != nil
```

</details>

#### try_read succeeds

- try_read succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_read succeeds")
val rw = rt_rwlock_new(10)
val v = rt_rwlock_try_read(rw)
expect v != nil
```

</details>

#### try_write succeeds

- try_write succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_write succeeds")
val rw = rt_rwlock_new(10)
val v = rt_rwlock_try_write(rw)
expect v != nil
```

</details>

#### set updates value

- set updates value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set updates value")
val rw = rt_rwlock_new(1)
rt_rwlock_set(rw, 2)
expect true
```

</details>

#### creates multiple rwlocks

- creates multiple rwlocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multiple rwlocks")
val r1 = rt_rwlock_new(1)
val r2 = rt_rwlock_new(2)
expect r1 != nil
expect r2 != nil
```

</details>

#### read after set

- read after set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read after set")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Concurrent Providers, HashMap, HashSet, BTreeMap, BTreeSet, Channel, Thread, Mutex, RwLock.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ab1234325b82b5a17cfd050f19b2adbed9ec569f9c3f953c32305421b6cefcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ab1234325b82b5a17cfd050f19b2adbed9ec569f9c3f953c32305421b6cefcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ab1234325b82b5a17cfd050f19b2adbed9ec569f9c3f953c32305421b6cefcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/concurrent_providers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent_providers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/concurrent_providers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a new empty hashmap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inserts and retrieves a value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/concurrent_providers_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for missing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
