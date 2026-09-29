# persistent_sorted_map_spec

> Purpose: Prove that PersistentSortedMap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 88 | 88 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# persistent_sorted_map_spec

Purpose: Prove that PersistentSortedMap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that PersistentSortedMap.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### PersistentSortedMap

### empty map

#### has zero length

- has zero length
- Verify: has zero length
   - Expected: m.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has zero length")
step("Verify: has zero length")
# @req: REQ-LIB-COMMON-001
val m = PersistentSortedMap.of_ints()
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### is empty

- is empty
- Verify: is empty
   - Expected: m.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is empty")
step("Verify: is empty")
val m = PersistentSortedMap.of_ints()
expect(m.is_empty()).to_equal(true)
```

</details>

#### get returns nil for any key

- get returns nil for any key
- Verify: get returns nil for any key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get returns nil for any key")
step("Verify: get returns nil for any key")
val m = PersistentSortedMap.of_ints()
expect(m.get(1)).to_be_nil()
expect(m.get(999)).to_be_nil()
```

</details>

#### get_or returns default for any key

- get_or returns default for any key
- Verify: get_or returns default for any key
   - Expected: m.get_or(1, 42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_or returns default for any key")
step("Verify: get_or returns default for any key")
val m = PersistentSortedMap.of_ints()
expect(m.get_or(1, 42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### contains returns false for any key

- contains returns false for any key
- Verify: contains returns false for any key
   - Expected: m does not contain `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("contains returns false for any key")
step("Verify: contains returns false for any key")
val m = PersistentSortedMap.of_ints()
expect(m.contains(1)).to_equal(false)
```

</details>

#### min_key returns nil

- min_key returns nil
- Verify: min_key returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("min_key returns nil")
step("Verify: min_key returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.min_key()).to_be_nil()
```

</details>

#### max_key returns nil

- max_key returns nil
- Verify: max_key returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("max_key returns nil")
step("Verify: max_key returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.max_key()).to_be_nil()
```

</details>

#### min_entry returns nil

- min_entry returns nil
- Verify: min_entry returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("min_entry returns nil")
step("Verify: min_entry returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.min_entry()).to_be_nil()
```

</details>

#### max_entry returns nil

- max_entry returns nil
- Verify: max_entry returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("max_entry returns nil")
step("Verify: max_entry returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.max_entry()).to_be_nil()
```

</details>

#### keys returns empty array

- keys returns empty array
- Verify: keys returns empty array
   - Expected: m.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keys returns empty array")
step("Verify: keys returns empty array")
val m = PersistentSortedMap.of_ints()
expect(m.keys().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### values returns empty array

- values returns empty array
- Verify: values returns empty array
   - Expected: m.values().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("values returns empty array")
step("Verify: values returns empty array")
val m = PersistentSortedMap.of_ints()
expect(m.values().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### entries returns empty array

- entries returns empty array
- Verify: entries returns empty array
   - Expected: m.entries().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("entries returns empty array")
step("Verify: entries returns empty array")
val m = PersistentSortedMap.of_ints()
expect(m.entries().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### set and get

#### stores and retrieves a single value

- stores and retrieves a single value
- Verify: stores and retrieves a single value
   - Expected: m.get(5) equals `five`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores and retrieves a single value")
step("Verify: stores and retrieves a single value")
val m = PersistentSortedMap.of_ints().set(5, "five")
expect(m.get(5)).to_equal("five")
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns new map on set - original unchanged

- returns new map on set - original unchanged
- Verify: returns new map on set - original unchanged
   - Expected: m1.len() equals `0`
   - Expected: m2.len() equals `1`
   - Expected: m2.get(1) equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns new map on set - original unchanged")
step("Verify: returns new map on set - original unchanged")
val m1 = PersistentSortedMap.of_ints()
val m2 = m1.set(1, "one")
expect(m1.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m1.get(1)).to_be_nil()
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.get(1)).to_equal("one")
```

</details>

#### overwrites existing key

- overwrites existing key
- Verify: overwrites existing key
   - Expected: m2.get(1) equals `new`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overwrites existing key")
step("Verify: overwrites existing key")
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = m1.set(1, "new")
expect(m2.get(1)).to_equal("new")
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### handles two keys

- handles two keys
- Verify: handles two keys
   - Expected: m.get(1) equals `one`
   - Expected: m.get(2) equals `two`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles two keys")
step("Verify: handles two keys")
val m = PersistentSortedMap.of_ints().set(1, "one").set(2, "two")
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles three keys

- handles three keys
- Verify: handles three keys
   - Expected: m.get(1) equals `a`
   - Expected: m.get(2) equals `b`
   - Expected: m.get(3) equals `c`
   - Expected: m.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles three keys")
step("Verify: handles three keys")
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
expect(m.get(1)).to_equal("a")
expect(m.get(2)).to_equal("b")
expect(m.get(3)).to_equal("c")
expect(m.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### returns nil for missing key

- returns nil for missing key
- Verify: returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for missing key")
step("Verify: returns nil for missing key")
val m = PersistentSortedMap.of_ints().set(1, "one")
expect(m.get(99)).to_be_nil()
```

</details>

#### is no longer empty after set

- is no longer empty after set
- Verify: is no longer empty after set
   - Expected: m.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is no longer empty after set")
step("Verify: is no longer empty after set")
val m = PersistentSortedMap.of_ints().set(1, "x")
expect(m.is_empty()).to_equal(false)
```

</details>

### text keys

#### stores and retrieves text keys

- stores and retrieves text keys
- Verify: stores and retrieves text keys
   - Expected: m.get("apple") equals `1`
   - Expected: m.get("banana") equals `2`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores and retrieves text keys")
step("Verify: stores and retrieves text keys")
val m = PersistentSortedMap.of_text().set("apple", 1).set("banana", 2)
expect(m.get("apple")).to_equal(1)
expect(m.get("banana")).to_equal(2)
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### maintains lexicographic order for text keys

- maintains lexicographic order for text keys
- Verify: maintains lexicographic order for text keys
   - Expected: k[0] equals `apple`
   - Expected: k[1] equals `banana`
   - Expected: k[2] equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maintains lexicographic order for text keys")
step("Verify: maintains lexicographic order for text keys")
val m = PersistentSortedMap.of_text().set("cherry", 3).set("apple", 1).set("banana", 2)
val k = m.keys()
expect(k[0]).to_equal("apple")
expect(k[1]).to_equal("banana")
expect(k[2]).to_equal("cherry")
```

</details>

### contains

#### returns true for existing key

- returns true for existing key
- Verify: returns true for existing key
   - Expected: m contains `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for existing key")
step("Verify: returns true for existing key")
val m = PersistentSortedMap.of_ints().set(10, "ten")
expect(m.contains(10)).to_equal(true)
```

</details>

#### returns false for missing key

- returns false for missing key
- Verify: returns false for missing key
   - Expected: m does not contain `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false for missing key")
step("Verify: returns false for missing key")
val m = PersistentSortedMap.of_ints().set(10, "ten")
expect(m.contains(20)).to_equal(false)
```

</details>

#### returns false after removal

- returns false after removal
- Verify: returns false after removal
   - Expected: m does not contain `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns false after removal")
step("Verify: returns false after removal")
val m = PersistentSortedMap.of_ints().set(10, "ten").remove(10)
expect(m.contains(10)).to_equal(false)
```

</details>

### get_or

#### returns value for existing key

- returns value for existing key
- Verify: returns value for existing key
   - Expected: m.get_or(1, "default") equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns value for existing key")
step("Verify: returns value for existing key")
val m = PersistentSortedMap.of_ints().set(1, "one")
expect(m.get_or(1, "default")).to_equal("one")
```

</details>

#### returns default for missing key

- returns default for missing key
- Verify: returns default for missing key
   - Expected: m.get_or(1, "default") equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default for missing key")
step("Verify: returns default for missing key")
val m = PersistentSortedMap.of_ints()
expect(m.get_or(1, "default")).to_equal("default")
```

</details>

#### returns default with numeric fallback

- returns default with numeric fallback
- Verify: returns default with numeric fallback
   - Expected: m.get_or(99, -1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns default with numeric fallback")
step("Verify: returns default with numeric fallback")
val m = PersistentSortedMap.of_ints()
expect(m.get_or(99, -1)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

### persistence

#### preserves snapshots across multiple sets

- preserves snapshots across multiple sets
- Verify: preserves snapshots across multiple sets
   - Expected: m0.len() equals `0`
   - Expected: m1.len() equals `1`
   - Expected: m2.len() equals `2`
   - Expected: m3.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves snapshots across multiple sets")
step("Verify: preserves snapshots across multiple sets")
val m0 = PersistentSortedMap.of_ints()
val m1 = m0.set(1, "a")
val m2 = m1.set(2, "b")
val m3 = m2.set(3, "c")
expect(m0.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m3.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(m1.get(2)).to_be_nil()
expect(m2.get(3)).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

- overwrite does not affect earlier version
- Verify: overwrite does not affect earlier version
   - Expected: m1.get(1) equals `old`
   - Expected: m2.get(1) equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overwrite does not affect earlier version")
step("Verify: overwrite does not affect earlier version")
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = m1.set(1, "new")
expect(m1.get(1)).to_equal("old")
expect(m2.get(1)).to_equal("new")
```

</details>

#### remove does not affect earlier version

- remove does not affect earlier version
- Verify: remove does not affect earlier version
   - Expected: m1.get(1) equals `a`
   - Expected: m1.len() equals `2`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("remove does not affect earlier version")
step("Verify: remove does not affect earlier version")
val m1 = PersistentSortedMap.of_ints().set(1, "a").set(2, "b")
val m2 = m1.remove(1)
expect(m1.get(1)).to_equal("a")
expect(m1.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m2.get(1)).to_be_nil()
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### remove

#### removes an existing key

- removes an existing key
- Verify: removes an existing key
   - Expected: m2.get(2) equals `b`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes an existing key")
step("Verify: removes an existing key")
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b")
val m2 = m.remove(1)
expect(m2.get(1)).to_be_nil()
expect(m2.get(2)).to_equal("b")
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### handles removing non-existent key

- handles removing non-existent key
- Verify: handles removing non-existent key
   - Expected: m2.len() equals `1`
   - Expected: m2.get(1) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles removing non-existent key")
step("Verify: handles removing non-existent key")
val m = PersistentSortedMap.of_ints().set(1, "a")
val m2 = m.remove(99)
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.get(1)).to_equal("a")
```

</details>

#### removes last key to get empty map

- removes last key to get empty map
- Verify: removes last key to get empty map
   - Expected: m2.len() equals `0`
   - Expected: m2.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes last key to get empty map")
step("Verify: removes last key to get empty map")
val m = PersistentSortedMap.of_ints().set(1, "only")
val m2 = m.remove(1)
expect(m2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m2.is_empty()).to_equal(true)
```

</details>

#### removes from multi-key map

- removes from multi-key map
- Verify: removes from multi-key map
   - Expected: m2.len() equals `2`
   - Expected: m2.get(1) equals `a`
   - Expected: m2.get(3) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes from multi-key map")
step("Verify: removes from multi-key map")
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val m2 = m.remove(2)
expect(m2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m2.get(1)).to_equal("a")
expect(m2.get(2)).to_be_nil()
expect(m2.get(3)).to_equal("c")
```

</details>

#### remove from empty map returns same empty map

- remove from empty map returns same empty map
- Verify: remove from empty map returns same empty map
   - Expected: m2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("remove from empty map returns same empty map")
step("Verify: remove from empty map returns same empty map")
val m = PersistentSortedMap.of_ints()
val m2 = m.remove(1)
expect(m2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### min and max

#### min_key returns smallest key

- min_key returns smallest key
- Verify: min_key returns smallest key
   - Expected: m.min_key() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("min_key returns smallest key")
step("Verify: min_key returns smallest key")
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i")
expect(m.min_key()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### max_key returns largest key

- max_key returns largest key
- Verify: max_key returns largest key
   - Expected: m.max_key() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("max_key returns largest key")
step("Verify: max_key returns largest key")
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i")
expect(m.max_key()).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### min_entry returns key-value pair for smallest key

- min_entry returns key-value pair for smallest key
- Verify: min_entry returns key-value pair for smallest key
   - Expected: entry[0] equals `1`
   - Expected: entry[1] equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("min_entry returns key-value pair for smallest key")
step("Verify: min_entry returns key-value pair for smallest key")
val m = PersistentSortedMap.of_ints().set(5, "five").set(1, "one").set(9, "nine")
val entry = m.min_entry()
expect(entry[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(entry[1]).to_equal("one")
```

</details>

#### max_entry returns key-value pair for largest key

- max_entry returns key-value pair for largest key
- Verify: max_entry returns key-value pair for largest key
   - Expected: entry[0] equals `9`
   - Expected: entry[1] equals `nine`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("max_entry returns key-value pair for largest key")
step("Verify: max_entry returns key-value pair for largest key")
val m = PersistentSortedMap.of_ints().set(5, "five").set(1, "one").set(9, "nine")
val entry = m.max_entry()
expect(entry[0]).to_equal(9)  # oracle: 9 — named expected value from the requirement
expect(entry[1]).to_equal("nine")
```

</details>

#### single element map has same min and max

- single element map has same min and max
- Verify: single element map has same min and max
   - Expected: m.min_key() equals `42`
   - Expected: m.max_key() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single element map has same min and max")
step("Verify: single element map has same min and max")
val m = PersistentSortedMap.of_ints().set(42, "answer")
expect(m.min_key()).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(m.max_key()).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### range

#### returns entries within range inclusive

- returns entries within range inclusive
- Verify: returns entries within range inclusive
   - Expected: r.len() equals `3`
   - Expected: r[0][0] equals `3`
   - Expected: r[1][0] equals `5`
   - Expected: r[2][0] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns entries within range inclusive")
step("Verify: returns entries within range inclusive")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e").set(7, "g").set(9, "i")
val r = m.range(3, 7)
expect(r.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(r[0][0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(r[1][0]).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(r[2][0]).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

#### returns empty for range with no matches

- returns empty for range with no matches
- Verify: returns empty for range with no matches
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty for range with no matches")
step("Verify: returns empty for range with no matches")
val m = PersistentSortedMap.of_ints().set(1, "a").set(10, "j")
val r = m.range(3, 7)
expect(r.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns single entry when from equals to

- returns single entry when from equals to
- Verify: returns single entry when from equals to
   - Expected: r.len() equals `1`
   - Expected: r[0][0] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns single entry when from equals to")
step("Verify: returns single entry when from equals to")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val r = m.range(3, 3)
expect(r.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(r[0][0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### range on empty map returns empty

- range on empty map returns empty
- Verify: range on empty map returns empty
   - Expected: r.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("range on empty map returns empty")
step("Verify: range on empty map returns empty")
val m = PersistentSortedMap.of_ints()
val r = m.range(1, 10)
expect(r.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns all entries when range covers entire map

- returns all entries when range covers entire map
- Verify: returns all entries when range covers entire map
   - Expected: r.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns all entries when range covers entire map")
step("Verify: returns all entries when range covers entire map")
val m = PersistentSortedMap.of_ints().set(2, "b").set(4, "d").set(6, "f")
val r = m.range(1, 10)
expect(r.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

### floor

#### returns exact match

- returns exact match
- Verify: returns exact match
   - Expected: f[0] equals `3`
   - Expected: f[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns exact match")
step("Verify: returns exact match")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val f = m.floor(3)
expect(f[0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(f[1]).to_equal("c")
```

</details>

#### returns greatest key less than target

- returns greatest key less than target
- Verify: returns greatest key less than target
   - Expected: f[0] equals `3`
   - Expected: f[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns greatest key less than target")
step("Verify: returns greatest key less than target")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val f = m.floor(4)
expect(f[0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(f[1]).to_equal("c")
```

</details>

#### returns nil when no key is less or equal

- returns nil when no key is less or equal
- Verify: returns nil when no key is less or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when no key is less or equal")
step("Verify: returns nil when no key is less or equal")
val m = PersistentSortedMap.of_ints().set(5, "e").set(10, "j")
val f = m.floor(3)
expect(f).to_be_nil()
```

</details>

#### floor on empty map returns nil

- floor on empty map returns nil
- Verify: floor on empty map returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("floor on empty map returns nil")
step("Verify: floor on empty map returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.floor(5)).to_be_nil()
```

</details>

### ceiling

#### returns exact match

- returns exact match
- Verify: returns exact match
   - Expected: c[0] equals `3`
   - Expected: c[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns exact match")
step("Verify: returns exact match")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val c = m.ceiling(3)
expect(c[0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(c[1]).to_equal("c")
```

</details>

#### returns smallest key greater than target

- returns smallest key greater than target
- Verify: returns smallest key greater than target
   - Expected: c[0] equals `3`
   - Expected: c[1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns smallest key greater than target")
step("Verify: returns smallest key greater than target")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c").set(5, "e")
val c = m.ceiling(2)
expect(c[0]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(c[1]).to_equal("c")
```

</details>

#### returns nil when no key is greater or equal

- returns nil when no key is greater or equal
- Verify: returns nil when no key is greater or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil when no key is greater or equal")
step("Verify: returns nil when no key is greater or equal")
val m = PersistentSortedMap.of_ints().set(1, "a").set(3, "c")
val c = m.ceiling(10)
expect(c).to_be_nil()
```

</details>

#### ceiling on empty map returns nil

- ceiling on empty map returns nil
- Verify: ceiling on empty map returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ceiling on empty map returns nil")
step("Verify: ceiling on empty map returns nil")
val m = PersistentSortedMap.of_ints()
expect(m.ceiling(5)).to_be_nil()
```

</details>

### ordered iteration

#### keys are in sorted order

- keys are in sorted order
- Verify: keys are in sorted order
   - Expected: k.len() equals `4`
   - Expected: k[0] equals `1`
   - Expected: k[1] equals `3`
   - Expected: k[2] equals `5`
   - Expected: k[3] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keys are in sorted order")
step("Verify: keys are in sorted order")
val m = PersistentSortedMap.of_ints().set(5, "e").set(1, "a").set(9, "i").set(3, "c")
val k = m.keys()
expect(k.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(k[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(k[1]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(k[2]).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(k[3]).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### values are in key-sorted order

- values are in key-sorted order
- Verify: values are in key-sorted order
   - Expected: v[0] equals `a`
   - Expected: v[1] equals `b`
   - Expected: v[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("values are in key-sorted order")
step("Verify: values are in key-sorted order")
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
val v = m.values()
expect(v[0]).to_equal("a")
expect(v[1]).to_equal("b")
expect(v[2]).to_equal("c")
```

</details>

#### entries are in key-sorted order

- entries are in key-sorted order
- Verify: entries are in key-sorted order
   - Expected: e.len() equals `3`
   - Expected: e[0][0] equals `10`
   - Expected: e[1][0] equals `20`
   - Expected: e[2][0] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("entries are in key-sorted order")
step("Verify: entries are in key-sorted order")
val m = PersistentSortedMap.of_ints().set(20, "x").set(10, "y").set(30, "z")
val e = m.entries()
expect(e.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(e[0][0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(e[1][0]).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(e[2][0]).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

### merge

#### merges two disjoint maps

- merges two disjoint maps
- Verify: merges two disjoint maps
   - Expected: merged.len() equals `4`
   - Expected: merged.get(1) equals `a`
   - Expected: merged.get(2) equals `b`
   - Expected: merged.get(3) equals `c`
   - Expected: merged.get(4) equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merges two disjoint maps")
step("Verify: merges two disjoint maps")
val m1 = PersistentSortedMap.of_ints().set(1, "a").set(3, "c")
val m2 = PersistentSortedMap.of_ints().set(2, "b").set(4, "d")
val merged = m1.merge(m2)
expect(merged.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(merged.get(1)).to_equal("a")
expect(merged.get(2)).to_equal("b")
expect(merged.get(3)).to_equal("c")
expect(merged.get(4)).to_equal("d")
```

</details>

#### other takes precedence on conflict

- other takes precedence on conflict
- Verify: other takes precedence on conflict
   - Expected: merged.get(1) equals `new`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("other takes precedence on conflict")
step("Verify: other takes precedence on conflict")
val m1 = PersistentSortedMap.of_ints().set(1, "old")
val m2 = PersistentSortedMap.of_ints().set(1, "new")
val merged = m1.merge(m2)
expect(merged.get(1)).to_equal("new")
expect(merged.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### merge with empty returns self

- merge with empty returns self
- Verify: merge with empty returns self
   - Expected: merged.get(1) equals `a`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merge with empty returns self")
step("Verify: merge with empty returns self")
val m1 = PersistentSortedMap.of_ints().set(1, "a")
val m2 = PersistentSortedMap.of_ints()
val merged = m1.merge(m2)
expect(merged.get(1)).to_equal("a")
expect(merged.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### empty merge with other returns other

- empty merge with other returns other
- Verify: empty merge with other returns other
   - Expected: merged.get(2) equals `b`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty merge with other returns other")
step("Verify: empty merge with other returns other")
val m1 = PersistentSortedMap.of_ints()
val m2 = PersistentSortedMap.of_ints().set(2, "b")
val merged = m1.merge(m2)
expect(merged.get(2)).to_equal("b")
expect(merged.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not modify originals

- does not modify originals
- Verify: does not modify originals
   - Expected: m1.len() equals `1`
   - Expected: m2.len() equals `1`
   - Expected: merged.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not modify originals")
step("Verify: does not modify originals")
val m1 = PersistentSortedMap.of_ints().set(1, "a")
val m2 = PersistentSortedMap.of_ints().set(2, "b")
val merged = m1.merge(m2)
expect(m1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(merged.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### merged map maintains sorted order

- merged map maintains sorted order
- Verify: merged map maintains sorted order
   - Expected: k[0] equals `1`
   - Expected: k[1] equals `3`
   - Expected: k[2] equals `5`
   - Expected: k[3] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("merged map maintains sorted order")
step("Verify: merged map maintains sorted order")
val m1 = PersistentSortedMap.of_ints().set(5, "e").set(1, "a")
val m2 = PersistentSortedMap.of_ints().set(3, "c").set(7, "g")
val merged = m1.merge(m2)
val k = merged.keys()
expect(k[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(k[1]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(k[2]).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(k[3]).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

### filter

#### keeps entries matching predicate

- keeps entries matching predicate
- Verify: keeps entries matching predicate
   - Expected: filtered.len() equals `2`
   - Expected: filtered.get(2) equals `20`
   - Expected: filtered.get(3) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps entries matching predicate")
step("Verify: keeps entries matching predicate")
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20).set(3, 30)
val filtered = m.filter(fn(k, v): v > 15)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(filtered.get(1)).to_be_nil()
expect(filtered.get(2)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(filtered.get(3)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### returns empty when nothing matches

- returns empty when nothing matches
- Verify: returns empty when nothing matches
   - Expected: filtered.len() equals `0`
   - Expected: filtered.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns empty when nothing matches")
step("Verify: returns empty when nothing matches")
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
val filtered = m.filter(fn(k, v): v > 100)
expect(filtered.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(filtered.is_empty()).to_equal(true)
```

</details>

#### returns all when everything matches

- returns all when everything matches
- Verify: returns all when everything matches
   - Expected: filtered.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns all when everything matches")
step("Verify: returns all when everything matches")
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
val filtered = m.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### filter by key

- filter by key
- Verify: filter by key
   - Expected: filtered.len() equals `2`
   - Expected: filtered does not contain `1`
   - Expected: filtered contains `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filter by key")
step("Verify: filter by key")
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val filtered = m.filter(fn(k, v): k > 1)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(filtered.contains(1)).to_equal(false)
expect(filtered.contains(2)).to_equal(true)
```

</details>

#### does not modify original

- does not modify original
- Verify: does not modify original
   - Expected: m.len() equals `2`
   - Expected: filtered.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not modify original")
step("Verify: does not modify original")
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20)
val filtered = m.filter(fn(k, v): v > 15)
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(filtered.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### fold

#### sums all values

- sums all values
- Verify: sums all values
   - Expected: total equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sums all values")
step("Verify: sums all values")
val m = PersistentSortedMap.of_ints().set(1, 10).set(2, 20).set(3, 30)
val total = m.fold(0, fn(acc, k, v): acc + v)
expect(total).to_equal(60)  # oracle: 60 — named expected value from the requirement
```

</details>

#### fold over empty returns init

- fold over empty returns init
- Verify: fold over empty returns init
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fold over empty returns init")
step("Verify: fold over empty returns init")
val m = PersistentSortedMap.of_ints()
val result = m.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### fold processes keys in sorted order

- fold processes keys in sorted order
- Verify: fold processes keys in sorted order
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fold processes keys in sorted order")
step("Verify: fold processes keys in sorted order")
val m = PersistentSortedMap.of_ints().set(3, "c").set(1, "a").set(2, "b")
val result = m.fold("", fn(acc, k, v): acc + v)
expect(result).to_equal("abc")
```

</details>

#### fold counts entries

- fold counts entries
- Verify: fold counts entries
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fold counts entries")
step("Verify: fold counts entries")
val m = PersistentSortedMap.of_ints().set(1, "a").set(2, "b").set(3, "c")
val count = m.fold(0, fn(acc, k, v): acc + 1)
expect(count).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

### from_entries

#### builds from key-value pairs

- builds from key-value pairs
- Verify: builds from key-value pairs
   - Expected: m.get(1) equals `one`
   - Expected: m.get(2) equals `two`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds from key-value pairs")
step("Verify: builds from key-value pairs")
val m = PersistentSortedMap.from_entries([[1, "one"], [2, "two"]], compare_ints)
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles empty entries

- handles empty entries
- Verify: handles empty entries
   - Expected: m.len() equals `0`
   - Expected: m.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty entries")
step("Verify: handles empty entries")
val m = PersistentSortedMap.from_entries([], compare_ints)
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.is_empty()).to_equal(true)
```

</details>

#### handles single entry

- handles single entry
- Verify: handles single entry
   - Expected: m.get(42) equals `answer`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles single entry")
step("Verify: handles single entry")
val m = PersistentSortedMap.from_entries([[42, "answer"]], compare_ints)
expect(m.get(42)).to_equal("answer")
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### last value wins for duplicate keys

- last value wins for duplicate keys
- Verify: last value wins for duplicate keys
   - Expected: m.get(1) equals `second`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("last value wins for duplicate keys")
step("Verify: last value wins for duplicate keys")
val m = PersistentSortedMap.from_entries([[1, "first"], [1, "second"]], compare_ints)
expect(m.get(1)).to_equal("second")
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### maintains sorted order from entries

- maintains sorted order from entries
- Verify: maintains sorted order from entries
   - Expected: k[0] equals `1`
   - Expected: k[1] equals `3`
   - Expected: k[2] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maintains sorted order from entries")
step("Verify: maintains sorted order from entries")
val m = PersistentSortedMap.from_entries([[5, "e"], [1, "a"], [3, "c"]], compare_ints)
val k = m.keys()
expect(k[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(k[1]).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(k[2]).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

### to_dict

#### converts to mutable dict

- converts to mutable dict
- Verify: converts to mutable dict
   - Expected: d[1] equals `one`
   - Expected: d[2] equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("converts to mutable dict")
step("Verify: converts to mutable dict")
val m = PersistentSortedMap.of_ints().set(1, "one").set(2, "two")
val d = m.to_dict()
expect(d[1]).to_equal("one")
expect(d[2]).to_equal("two")
```

</details>

#### empty map converts to empty dict

- empty map converts to empty dict
- Verify: empty map converts to empty dict
   - Expected: d.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty map converts to empty dict")
step("Verify: empty map converts to empty dict")
val m = PersistentSortedMap.of_ints()
val d = m.to_dict()
expect(d.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### factory functions

#### of_ints creates empty int map

- of_ints creates empty int map
- Verify: of_ints creates empty int map
   - Expected: m.len() equals `0`
   - Expected: m2.get(1) equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("of_ints creates empty int map")
step("Verify: of_ints creates empty int map")
val m = PersistentSortedMap.of_ints()
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
val m2 = m.set(1, "one")
expect(m2.get(1)).to_equal("one")
```

</details>

#### of_text creates empty text map

- of_text creates empty text map
- Verify: of_text creates empty text map
   - Expected: m.len() equals `0`
   - Expected: m2.get("hello") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("of_text creates empty text map")
step("Verify: of_text creates empty text map")
val m = PersistentSortedMap.of_text()
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
val m2 = m.set("hello", 1)
expect(m2.get("hello")).to_equal(1)
```

</details>

#### empty with custom comparator

- empty with custom comparator
- Verify: empty with custom comparator
   - Expected: k[0] equals `1`
   - Expected: k[1] equals `2`
   - Expected: k[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty with custom comparator")
step("Verify: empty with custom comparator")
val m = PersistentSortedMap.empty(compare_ints)
val m2 = m.set(3, "c").set(1, "a").set(2, "b")
val k = m2.keys()
expect(k[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(k[1]).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(k[2]).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

### stress test

#### handles many insertions via helper fn

- handles many insertions via helper fn
- Verify: handles many insertions via helper fn
   - Expected: run_insert_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles many insertions via helper fn")
step("Verify: handles many insertions via helper fn")
fn run_insert_stress() -> i64:
    var m = PersistentSortedMap.of_ints()
    var i = 0
    while i < 100:
        m = m.set(i, i * 10)
        i = i + 1
    m.len()
expect(run_insert_stress()).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>

#### set and get many elements

- set and get many elements
- Verify: set and get many elements
   - Expected: run_get_stress() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set and get many elements")
step("Verify: set and get many elements")
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
expect(run_get_stress()).to_equal(50)  # oracle: 50 — named expected value from the requirement
```

</details>

#### remove many elements

- remove many elements
- Verify: remove many elements
   - Expected: run_remove_stress() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("remove many elements")
step("Verify: remove many elements")
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
expect(run_remove_stress()).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### keys stay sorted after many random-order inserts

- keys stay sorted after many random-order inserts
- Verify: keys stay sorted after many random-order inserts
   - Expected: run_order_stress() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keys stay sorted after many random-order inserts")
step("Verify: keys stay sorted after many random-order inserts")
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

- set same key same value returns equivalent map
- Verify: set same key same value returns equivalent map
   - Expected: m2.get(1) equals `a`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("set same key same value returns equivalent map")
step("Verify: set same key same value returns equivalent map")
val m = PersistentSortedMap.of_ints().set(1, "a")
val m2 = m.set(1, "a")
expect(m2.get(1)).to_equal("a")
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### single entry map operations

- single entry map operations
- Verify: single entry map operations
   - Expected: m.len() equals `1`
   - Expected: m.min_key() equals `42`
   - Expected: m.max_key() equals `42`
   - Expected: r.len() equals `1`
   - Expected: f[0] equals `42`
   - Expected: c[0] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single entry map operations")
step("Verify: single entry map operations")
val m = PersistentSortedMap.of_ints().set(42, "answer")
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m.min_key()).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(m.max_key()).to_equal(42)  # oracle: 42 — named expected value from the requirement
val r = m.range(1, 100)
expect(r.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val f = m.floor(42)
expect(f[0]).to_equal(42)  # oracle: 42 — named expected value from the requirement
val c = m.ceiling(42)
expect(c[0]).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### negative integer keys

- negative integer keys
- Verify: negative integer keys
   - Expected: m.get(-5) equals `neg5`
   - Expected: m.min_key() equals `-5`
   - Expected: m.max_key() equals `5`
   - Expected: k[0] equals `-5`
   - Expected: k[1] equals `0`
   - Expected: k[2] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("negative integer keys")
step("Verify: negative integer keys")
val m = PersistentSortedMap.of_ints().set(-5, "neg5").set(0, "zero").set(5, "pos5")
expect(m.get(-5)).to_equal("neg5")
expect(m.min_key()).to_equal(-5)  # oracle: -5 — named expected value from the requirement
expect(m.max_key()).to_equal(5)  # oracle: 5 — named expected value from the requirement
val k = m.keys()
expect(k[0]).to_equal(-5)  # oracle: -5 — named expected value from the requirement
expect(k[1]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(k[2]).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 88 |
| Active scenarios | 88 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d47a084beb013547063991f917b28e1a03fba376c7d4623b58b4083f73188bb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d47a084beb013547063991f917b28e1a03fba376c7d4623b58b4083f73188bb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d47a084beb013547063991f917b28e1a03fba376c7d4623b58b4083f73188bb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl
mirror: doc/06_spec/01_unit/lib/common/immut/persistent_sorted_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/immut/persistent_sorted_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/immut/persistent_sorted_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has zero length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/immut/persistent_sorted_map_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get returns nil for any key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
