# persistent_map_spec

> Purpose: Prove that PersistentMap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# persistent_map_spec

Purpose: Prove that PersistentMap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/immut/persistent_map_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that PersistentMap.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### PersistentMap

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
# @req REQ-SSPEC-UNIT
step("has zero length")
step("Verify: has zero length")
# @req: REQ-LIB-COMMON-001
val m = PersistentMap.empty()
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
# @req REQ-SSPEC-UNIT
step("is empty")
step("Verify: is empty")
val m = PersistentMap.empty()
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
# @req REQ-SSPEC-UNIT
step("get returns nil for any key")
step("Verify: get returns nil for any key")
val m = PersistentMap.empty()
expect(m.get("key")).to_be_nil()
expect(m.get("anything")).to_be_nil()
```

</details>

#### contains returns false for any key

- contains returns false for any key
- Verify: contains returns false for any key
   - Expected: m does not contain `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains returns false for any key")
step("Verify: contains returns false for any key")
val m = PersistentMap.empty()
expect(m.contains("x")).to_equal(false)
```

</details>

#### keys returns empty array

- keys returns empty array
- Verify: keys returns empty array
   - Expected: k.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys returns empty array")
step("Verify: keys returns empty array")
val m = PersistentMap.empty()
val k = m.keys()
expect(k.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### values returns empty array

- values returns empty array
- Verify: values returns empty array
   - Expected: v.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values returns empty array")
step("Verify: values returns empty array")
val m = PersistentMap.empty()
val v = m.values()
expect(v.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### entries returns empty array

- entries returns empty array
- Verify: entries returns empty array
   - Expected: e.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries returns empty array")
step("Verify: entries returns empty array")
val m = PersistentMap.empty()
val e = m.entries()
expect(e.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### set and get

#### stores and retrieves a single value

- stores and retrieves a single value
- Verify: stores and retrieves a single value
   - Expected: m.get("a") equals `1`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores and retrieves a single value")
step("Verify: stores and retrieves a single value")
val m = PersistentMap.empty().set("a", 1)
expect(m.get("a")).to_equal(1)
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns new map on set - original unchanged

- returns new map on set - original unchanged
- Verify: returns new map on set - original unchanged
   - Expected: m1.len() equals `0`
   - Expected: m2.len() equals `1`
   - Expected: m2.get("a") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns new map on set - original unchanged")
step("Verify: returns new map on set - original unchanged")
val m1 = PersistentMap.empty()
val m2 = m1.set("a", 1)
expect(m1.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m1.get("a")).to_be_nil()
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.get("a")).to_equal(1)
```

</details>

#### overwrites existing key with same length

- overwrites existing key with same length
- Verify: overwrites existing key with same length
   - Expected: m.get("a") equals `2`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites existing key with same length")
step("Verify: overwrites existing key with same length")
val m = PersistentMap.empty().set("a", 1).set("a", 2)
expect(m.get("a")).to_equal(2)
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### handles two keys

- handles two keys
- Verify: handles two keys
   - Expected: m.get("a") equals `1`
   - Expected: m.get("b") equals `2`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles two keys")
step("Verify: handles two keys")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles three keys

- handles three keys
- Verify: handles three keys
   - Expected: m.get("a") equals `1`
   - Expected: m.get("b") equals `2`
   - Expected: m.get("c") equals `3`
   - Expected: m.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles three keys")
step("Verify: handles three keys")
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
expect(m.get("c")).to_equal(3)
expect(m.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### stores text values

- stores text values
- Verify: stores text values
   - Expected: m.get("name") equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores text values")
step("Verify: stores text values")
val m = PersistentMap.empty().set("name", "Alice")
expect(m.get("name")).to_equal("Alice")
```

</details>

#### stores integer keys

- stores integer keys
- Verify: stores integer keys
   - Expected: m.get(1) equals `one`
   - Expected: m.get(2) equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores integer keys")
step("Verify: stores integer keys")
val m = PersistentMap.empty().set(1, "one").set(2, "two")
expect(m.get(1)).to_equal("one")
expect(m.get(2)).to_equal("two")
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
# @req REQ-SSPEC-UNIT
step("returns nil for missing key")
step("Verify: returns nil for missing key")
val m = PersistentMap.empty().set("a", 1)
expect(m.get("b")).to_be_nil()
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
# @req REQ-SSPEC-UNIT
step("is no longer empty after set")
step("Verify: is no longer empty after set")
val m = PersistentMap.empty().set("x", 42)
expect(m.is_empty()).to_equal(false)
```

</details>

### persistence across multiple sets

#### preserves snapshots

- preserves snapshots
- Verify: preserves snapshots
   - Expected: m0.len() equals `0`
   - Expected: m1.len() equals `1`
   - Expected: m2.len() equals `2`
   - Expected: m3.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves snapshots")
step("Verify: preserves snapshots")
val m0 = PersistentMap.empty()
val m1 = m0.set("a", 1)
val m2 = m1.set("b", 2)
val m3 = m2.set("c", 3)
expect(m0.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m3.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(m1.get("b")).to_be_nil()
expect(m2.get("c")).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

- overwrite does not affect earlier version
- Verify: overwrite does not affect earlier version
   - Expected: m1.get("key") equals `old`
   - Expected: m2.get("key") equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrite does not affect earlier version")
step("Verify: overwrite does not affect earlier version")
val m1 = PersistentMap.empty().set("key", "old")
val m2 = m1.set("key", "new")
expect(m1.get("key")).to_equal("old")
expect(m2.get("key")).to_equal("new")
```

</details>

### remove

#### removes an existing key

- removes an existing key
- Verify: removes an existing key
   - Expected: m2.get("b") equals `2`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes an existing key")
step("Verify: removes an existing key")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val m2 = m.remove("a")
expect(m2.get("a")).to_be_nil()
expect(m2.get("b")).to_equal(2)
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### does not modify original on remove

- does not modify original on remove
- Verify: does not modify original on remove
   - Expected: m1.get("a") equals `1`
   - Expected: m1.len() equals `1`
   - Expected: m2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not modify original on remove")
step("Verify: does not modify original on remove")
val m1 = PersistentMap.empty().set("a", 1)
val m2 = m1.remove("a")
expect(m1.get("a")).to_equal(1)
expect(m1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.get("a")).to_be_nil()
expect(m2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### handles removing non-existent key

- handles removing non-existent key
- Verify: handles removing non-existent key
   - Expected: m2.len() equals `1`
   - Expected: m2.get("a") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles removing non-existent key")
step("Verify: handles removing non-existent key")
val m = PersistentMap.empty().set("a", 1)
val m2 = m.remove("b")
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.get("a")).to_equal(1)
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
# @req REQ-SSPEC-UNIT
step("removes last key to get empty map")
step("Verify: removes last key to get empty map")
val m = PersistentMap.empty().set("only", 99)
val m2 = m.remove("only")
expect(m2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m2.is_empty()).to_equal(true)
```

</details>

#### removes from multi-key map

- removes from multi-key map
- Verify: removes from multi-key map
   - Expected: m2.len() equals `2`
   - Expected: m2.get("a") equals `1`
   - Expected: m2.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes from multi-key map")
step("Verify: removes from multi-key map")
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val m2 = m.remove("b")
expect(m2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(m2.get("a")).to_equal(1)
expect(m2.get("b")).to_be_nil()
expect(m2.get("c")).to_equal(3)
```

</details>

### contains

#### returns true for existing key

- returns true for existing key
- Verify: returns true for existing key
   - Expected: m contains `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for existing key")
step("Verify: returns true for existing key")
val m = PersistentMap.empty().set("x", 42)
expect(m.contains("x")).to_equal(true)
```

</details>

#### returns false for missing key

- returns false for missing key
- Verify: returns false for missing key
   - Expected: m does not contain `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for missing key")
step("Verify: returns false for missing key")
val m = PersistentMap.empty().set("x", 42)
expect(m.contains("y")).to_equal(false)
```

</details>

#### returns false after removal

- returns false after removal
- Verify: returns false after removal
   - Expected: m does not contain `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false after removal")
step("Verify: returns false after removal")
val m = PersistentMap.empty().set("x", 42).remove("x")
expect(m.contains("x")).to_equal(false)
```

</details>

### get_or

#### returns default for missing key

- returns default for missing key
- Verify: returns default for missing key
   - Expected: m.get_or("x", 42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default for missing key")
step("Verify: returns default for missing key")
val m = PersistentMap.empty()
expect(m.get_or("x", 42)).to_equal(42)
```

</details>

#### returns value for existing key

- returns value for existing key
- Verify: returns value for existing key
   - Expected: m.get_or("x", 42) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value for existing key")
step("Verify: returns value for existing key")
val m = PersistentMap.empty().set("x", 10)
expect(m.get_or("x", 42)).to_equal(10)
```

</details>

#### returns default with text fallback

- returns default with text fallback
- Verify: returns default with text fallback
   - Expected: m.get_or("name", "unknown") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default with text fallback")
step("Verify: returns default with text fallback")
val m = PersistentMap.empty()
expect(m.get_or("name", "unknown")).to_equal("unknown")
```

</details>

### from_entries

#### builds from key-value pairs

- builds from key-value pairs
- Verify: builds from key-value pairs
   - Expected: m.get("a") equals `1`
   - Expected: m.get("b") equals `2`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds from key-value pairs")
step("Verify: builds from key-value pairs")
val m = PersistentMap.from_entries([["a", 1], ["b", 2]])
expect(m.get("a")).to_equal(1)
expect(m.get("b")).to_equal(2)
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
# @req REQ-SSPEC-UNIT
step("handles empty entries")
step("Verify: handles empty entries")
val m = PersistentMap.from_entries([])
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.is_empty()).to_equal(true)
```

</details>

#### handles single entry

- handles single entry
- Verify: handles single entry
   - Expected: m.get("only") equals `99`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single entry")
step("Verify: handles single entry")
val m = PersistentMap.from_entries([["only", 99]])
expect(m.get("only")).to_equal(99)
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### last value wins for duplicate keys

- last value wins for duplicate keys
- Verify: last value wins for duplicate keys
   - Expected: m.get("a") equals `2`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last value wins for duplicate keys")
step("Verify: last value wins for duplicate keys")
val m = PersistentMap.from_entries([["a", 1], ["a", 2]])
expect(m.get("a")).to_equal(2)
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### from_dict

#### builds from mutable dict

- builds from mutable dict
- Verify: builds from mutable dict
   - Expected: m.get("x") equals `10`
   - Expected: m.get("y") equals `20`
   - Expected: m.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds from mutable dict")
step("Verify: builds from mutable dict")
var d = {}
d["x"] = 10
d["y"] = 20
val m = PersistentMap.from_dict(d)
expect(m.get("x")).to_equal(10)
expect(m.get("y")).to_equal(20)
expect(m.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles empty dict

- handles empty dict
- Verify: handles empty dict
   - Expected: m.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty dict")
step("Verify: handles empty dict")
val d = {}
val m = PersistentMap.from_dict(d)
expect(m.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### keys and values

#### returns correct number of keys

- returns correct number of keys
- Verify: returns correct number of keys
   - Expected: k.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct number of keys")
step("Verify: returns correct number of keys")
val m = PersistentMap.empty().set("x", 1).set("y", 2)
val k = m.keys()
expect(k.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns correct number of values

- returns correct number of values
- Verify: returns correct number of values
   - Expected: v.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct number of values")
step("Verify: returns correct number of values")
val m = PersistentMap.empty().set("x", 10).set("y", 20)
val v = m.values()
expect(v.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### single key map

- single key map
- Verify: single key map
   - Expected: k.len() equals `1`
   - Expected: v.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single key map")
step("Verify: single key map")
val m = PersistentMap.empty().set("only", 42)
val k = m.keys()
val v = m.values()
expect(k.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(v.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### entries

#### returns key-value pairs

- returns key-value pairs
- Verify: returns key-value pairs
   - Expected: e.len() equals `1`
   - Expected: pair[0] equals `a`
   - Expected: pair[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns key-value pairs")
step("Verify: returns key-value pairs")
val m = PersistentMap.empty().set("a", 1)
val e = m.entries()
expect(e.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val pair = e[0]
expect(pair[0]).to_equal("a")
expect(pair[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns correct count for multi-entry map

- returns correct count for multi-entry map
- Verify: returns correct count for multi-entry map
   - Expected: e.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct count for multi-entry map")
step("Verify: returns correct count for multi-entry map")
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val e = m.entries()
expect(e.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

### merge

#### merges two disjoint maps

- merges two disjoint maps
- Verify: merges two disjoint maps
   - Expected: merged.get("a") equals `1`
   - Expected: merged.get("b") equals `2`
   - Expected: merged.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merges two disjoint maps")
step("Verify: merges two disjoint maps")
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(1)
expect(merged.get("b")).to_equal(2)
expect(merged.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### other takes precedence on conflict

- other takes precedence on conflict
- Verify: other takes precedence on conflict
   - Expected: merged.get("a") equals `99`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("other takes precedence on conflict")
step("Verify: other takes precedence on conflict")
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("a", 99)
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(99)
expect(merged.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### merge with empty returns self

- merge with empty returns self
- Verify: merge with empty returns self
   - Expected: merged.get("a") equals `1`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("merge with empty returns self")
step("Verify: merge with empty returns self")
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty()
val merged = m1.merge(m2)
expect(merged.get("a")).to_equal(1)
expect(merged.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### empty merge with other returns other

- empty merge with other returns other
- Verify: empty merge with other returns other
   - Expected: merged.get("b") equals `2`
   - Expected: merged.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty merge with other returns other")
step("Verify: empty merge with other returns other")
val m1 = PersistentMap.empty()
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(merged.get("b")).to_equal(2)
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
# @req REQ-SSPEC-UNIT
step("does not modify originals")
step("Verify: does not modify originals")
val m1 = PersistentMap.empty().set("a", 1)
val m2 = PersistentMap.empty().set("b", 2)
val merged = m1.merge(m2)
expect(m1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(merged.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### filter

#### keeps entries matching predicate

- keeps entries matching predicate
- Verify: keeps entries matching predicate
   - Expected: filtered.len() equals `2`
   - Expected: filtered.get("b") equals `2`
   - Expected: filtered.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps entries matching predicate")
step("Verify: keeps entries matching predicate")
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val filtered = m.filter(fn(k, v): v > 1)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(filtered.get("a")).to_be_nil()
expect(filtered.get("b")).to_equal(2)
expect(filtered.get("c")).to_equal(3)
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
# @req REQ-SSPEC-UNIT
step("returns empty when nothing matches")
step("Verify: returns empty when nothing matches")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
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
# @req REQ-SSPEC-UNIT
step("returns all when everything matches")
step("Verify: returns all when everything matches")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val filtered = m.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### map_values

#### transforms all values

- transforms all values
- Verify: transforms all values
   - Expected: doubled.get("a") equals `2`
   - Expected: doubled.get("b") equals `4`
   - Expected: doubled.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transforms all values")
step("Verify: transforms all values")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val doubled = m.map_values(fn(v): v * 2)
expect(doubled.get("a")).to_equal(2)
expect(doubled.get("b")).to_equal(4)
expect(doubled.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### does not modify original

- does not modify original
- Verify: does not modify original
   - Expected: m.get("a") equals `5`
   - Expected: mapped.get("a") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not modify original")
step("Verify: does not modify original")
val m = PersistentMap.empty().set("a", 5)
val mapped = m.map_values(fn(v): v + 10)
expect(m.get("a")).to_equal(5)
expect(mapped.get("a")).to_equal(15)
```

</details>

### fold

#### sums all values

- sums all values
- Verify: sums all values
   - Expected: total equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums all values")
step("Verify: sums all values")
val m = PersistentMap.empty().set("a", 1).set("b", 2).set("c", 3)
val total = m.fold(0, fn(acc, k, v): acc + v)
expect(total).to_equal(6)  # oracle: 6 — named expected value from the requirement
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
# @req REQ-SSPEC-UNIT
step("fold over empty returns init")
step("Verify: fold over empty returns init")
val m = PersistentMap.empty()
val result = m.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

### update

#### updates existing key

- updates existing key
- Verify: updates existing key
   - Expected: m2.get("count") equals `6`
   - Expected: m.get("count") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates existing key")
step("Verify: updates existing key")
val m = PersistentMap.empty().set("count", 5)
val m2 = m.update("count", fn(v): v + 1)
expect(m2.get("count")).to_equal(6)
expect(m.get("count")).to_equal(5)
```

</details>

#### creates key when missing

- creates key when missing
- Verify: creates key when missing
   - Expected: m2.get("new") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates key when missing")
step("Verify: creates key when missing")
val m = PersistentMap.empty()
val m2 = m.update("new", fn(v): 42)
expect(m2.get("new")).to_equal(42)
```

</details>

### copy

#### returns identical map

- returns identical map
- Verify: returns identical map
   - Expected: c.get("a") equals `1`
   - Expected: c.get("b") equals `2`
   - Expected: c.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns identical map")
step("Verify: returns identical map")
val m = PersistentMap.empty().set("a", 1).set("b", 2)
val c = m.copy()
expect(c.get("a")).to_equal(1)
expect(c.get("b")).to_equal(2)
expect(c.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### to_dict

#### converts to mutable dict

- converts to mutable dict
- Verify: converts to mutable dict
   - Expected: d["x"] equals `10`
   - Expected: d["y"] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to mutable dict")
step("Verify: converts to mutable dict")
val m = PersistentMap.empty().set("x", 10).set("y", 20)
val d = m.to_dict()
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
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
# @req REQ-SSPEC-UNIT
step("empty map converts to empty dict")
step("Verify: empty map converts to empty dict")
val m = PersistentMap.empty()
val d = m.to_dict()
expect(d.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### stress test

#### handles many elements via helper fn

- handles many elements via helper fn
- Verify: handles many elements via helper fn
   - Expected: run_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many elements via helper fn")
step("Verify: handles many elements via helper fn")
fn run_stress() -> i64:
    var m = PersistentMap.empty()
    var i = 0
    while i < 100:
        m = m.set("key_{i}", i)
        i = i + 1
    m.len()
expect(run_stress()).to_equal(100)  # oracle: 100 — named expected value from the requirement
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
# @req REQ-SSPEC-UNIT
step("set and get many elements")
step("Verify: set and get many elements")
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
# @req REQ-SSPEC-UNIT
step("remove many elements")
step("Verify: remove many elements")
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
expect(run_remove_stress()).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

### edge cases

#### set same key same value returns same map

- set same key same value returns same map
- Verify: set same key same value returns same map
   - Expected: m2.get("a") equals `1`
   - Expected: m2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set same key same value returns same map")
step("Verify: set same key same value returns same map")
val m = PersistentMap.empty().set("a", 1)
val m2 = m.set("a", 1)
expect(m2.get("a")).to_equal(1)
expect(m2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### empty key string

- empty key string
- Verify: empty key string
   - Expected: m.get("") equals `empty_key`
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty key string")
step("Verify: empty key string")
val m = PersistentMap.empty().set("", "empty_key")
expect(m.get("")).to_equal("empty_key")
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### nil value stored and retrieved

- nil value stored and retrieved
- Verify: nil value stored and retrieved
   - Expected: m.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil value stored and retrieved")
step("Verify: nil value stored and retrieved")
val m = PersistentMap.empty().set("nil_val", nil)
expect(m.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### remove from empty map

- remove from empty map
- Verify: remove from empty map
   - Expected: m2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove from empty map")
step("Verify: remove from empty map")
val m = PersistentMap.empty()
val m2 = m.remove("nothing")
expect(m2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4eb90f0bd6239aaa6c75ffd82e6fb8431344664fb6509adde7b8949c5a6b804f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4eb90f0bd6239aaa6c75ffd82e6fb8431344664fb6509adde7b8949c5a6b804f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4eb90f0bd6239aaa6c75ffd82e6fb8431344664fb6509adde7b8949c5a6b804f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/immut/persistent_map_spec.spl
mirror: doc/06_spec/unit/lib/common/immut/persistent_map_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/immut/persistent_map_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/immut/persistent_map_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/immut/persistent_map_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 40 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/immut/persistent_map_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has zero length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_map_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_map_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get returns nil for any key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
