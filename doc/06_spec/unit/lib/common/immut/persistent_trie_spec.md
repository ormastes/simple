# persistent_trie_spec

> Purpose: Prove that PersistentTrie.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# persistent_trie_spec

Purpose: Prove that PersistentTrie.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/immut/persistent_trie_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that PersistentTrie.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### PersistentTrie

### empty trie

#### has zero length

- has zero length
- Verify: has zero length
   - Expected: t.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has zero length")
step("Verify: has zero length")
# @req: REQ-LIB-COMMON-001
val t = PersistentTrie.empty()
expect(t.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### is empty

- is empty
- Verify: is empty
   - Expected: t.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is empty")
step("Verify: is empty")
val t = PersistentTrie.empty()
expect(t.is_empty()).to_equal(true)
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
val t = PersistentTrie.empty()
expect(t.get("hello")).to_be_nil()
expect(t.get("")).to_be_nil()
```

</details>

#### get_or returns default for any key

- get_or returns default for any key
- Verify: get_or returns default for any key
   - Expected: t.get_or("hello", 42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_or returns default for any key")
step("Verify: get_or returns default for any key")
val t = PersistentTrie.empty()
expect(t.get_or("hello", 42)).to_equal(42)
```

</details>

#### contains returns false for any key

- contains returns false for any key
- Verify: contains returns false for any key
   - Expected: t does not contain `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains returns false for any key")
step("Verify: contains returns false for any key")
val t = PersistentTrie.empty()
expect(t.contains("hello")).to_equal(false)
```

</details>

#### keys returns empty array

- keys returns empty array
- Verify: keys returns empty array
   - Expected: t.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys returns empty array")
step("Verify: keys returns empty array")
val t = PersistentTrie.empty()
expect(t.keys().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### values returns empty array

- values returns empty array
- Verify: values returns empty array
   - Expected: t.values().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values returns empty array")
step("Verify: values returns empty array")
val t = PersistentTrie.empty()
expect(t.values().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### entries returns empty array

- entries returns empty array
- Verify: entries returns empty array
   - Expected: t.entries().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries returns empty array")
step("Verify: entries returns empty array")
val t = PersistentTrie.empty()
expect(t.entries().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### keys_with_prefix returns empty on empty trie

- keys_with_prefix returns empty on empty trie
- Verify: keys_with_prefix returns empty on empty trie
   - Expected: t.keys_with_prefix("any").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys_with_prefix returns empty on empty trie")
step("Verify: keys_with_prefix returns empty on empty trie")
val t = PersistentTrie.empty()
expect(t.keys_with_prefix("any").len()).to_equal(0)
```

</details>

#### longest_prefix returns nil on empty trie

- longest_prefix returns nil on empty trie
- Verify: longest_prefix returns nil on empty trie


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("longest_prefix returns nil on empty trie")
step("Verify: longest_prefix returns nil on empty trie")
val t = PersistentTrie.empty()
expect(t.longest_prefix("anything")).to_be_nil()
```

</details>

### set and get

#### stores and retrieves a single value

- stores and retrieves a single value
- Verify: stores and retrieves a single value
   - Expected: t.get("hello") equals `1`
   - Expected: t.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores and retrieves a single value")
step("Verify: stores and retrieves a single value")
val t = PersistentTrie.empty().set("hello", 1)
expect(t.get("hello")).to_equal(1)
expect(t.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns new trie on set - original unchanged

- returns new trie on set - original unchanged
- Verify: returns new trie on set - original unchanged
   - Expected: t1.len() equals `0`
   - Expected: t2.len() equals `1`
   - Expected: t2.get("key") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns new trie on set - original unchanged")
step("Verify: returns new trie on set - original unchanged")
val t1 = PersistentTrie.empty()
val t2 = t1.set("key", 42)
expect(t1.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(t1.get("key")).to_be_nil()
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(t2.get("key")).to_equal(42)
```

</details>

#### overwrites existing key

- overwrites existing key
- Verify: overwrites existing key
   - Expected: t2.get("key") equals `new`
   - Expected: t2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites existing key")
step("Verify: overwrites existing key")
val t1 = PersistentTrie.empty().set("key", "old")
val t2 = t1.set("key", "new")
expect(t2.get("key")).to_equal("new")
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### handles two keys

- handles two keys
- Verify: handles two keys
   - Expected: t.get("apple") equals `1`
   - Expected: t.get("banana") equals `2`
   - Expected: t.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles two keys")
step("Verify: handles two keys")
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2)
expect(t.get("apple")).to_equal(1)
expect(t.get("banana")).to_equal(2)
expect(t.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles keys sharing prefix

- handles keys sharing prefix
- Verify: handles keys sharing prefix
   - Expected: t.get("app") equals `1`
   - Expected: t.get("apple") equals `2`
   - Expected: t.get("application") equals `3`
   - Expected: t.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles keys sharing prefix")
step("Verify: handles keys sharing prefix")
val t = PersistentTrie.empty().set("app", 1).set("apple", 2).set("application", 3)
expect(t.get("app")).to_equal(1)
expect(t.get("apple")).to_equal(2)
expect(t.get("application")).to_equal(3)
expect(t.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
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
val t = PersistentTrie.empty().set("hello", 1)
expect(t.get("world")).to_be_nil()
```

</details>

#### returns nil for partial prefix key

- returns nil for partial prefix key
- Verify: returns nil for partial prefix key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for partial prefix key")
step("Verify: returns nil for partial prefix key")
val t = PersistentTrie.empty().set("apple", 1)
expect(t.get("app")).to_be_nil()
```

</details>

#### is no longer empty after set

- is no longer empty after set
- Verify: is no longer empty after set
   - Expected: t.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is no longer empty after set")
step("Verify: is no longer empty after set")
val t = PersistentTrie.empty().set("x", 1)
expect(t.is_empty()).to_equal(false)
```

</details>

#### stores integer values

- stores integer values
- Verify: stores integer values
   - Expected: t.get("count") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores integer values")
step("Verify: stores integer values")
val t = PersistentTrie.empty().set("count", 42)
expect(t.get("count")).to_equal(42)
```

</details>

#### stores text values

- stores text values
- Verify: stores text values
   - Expected: t.get("name") equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores text values")
step("Verify: stores text values")
val t = PersistentTrie.empty().set("name", "Alice")
expect(t.get("name")).to_equal("Alice")
```

</details>

### contains

#### returns true for existing key

- returns true for existing key
- Verify: returns true for existing key
   - Expected: t contains `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for existing key")
step("Verify: returns true for existing key")
val t = PersistentTrie.empty().set("hello", 1)
expect(t.contains("hello")).to_equal(true)
```

</details>

#### returns false for missing key

- returns false for missing key
- Verify: returns false for missing key
   - Expected: t does not contain `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for missing key")
step("Verify: returns false for missing key")
val t = PersistentTrie.empty().set("hello", 1)
expect(t.contains("world")).to_equal(false)
```

</details>

#### returns false for prefix of existing key

- returns false for prefix of existing key
- Verify: returns false for prefix of existing key
   - Expected: t does not contain `app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for prefix of existing key")
step("Verify: returns false for prefix of existing key")
val t = PersistentTrie.empty().set("apple", 1)
expect(t.contains("app")).to_equal(false)
```

</details>

#### returns false after removal

- returns false after removal
- Verify: returns false after removal
   - Expected: t does not contain `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false after removal")
step("Verify: returns false after removal")
val t = PersistentTrie.empty().set("hello", 1).remove("hello")
expect(t.contains("hello")).to_equal(false)
```

</details>

#### returns true when key is prefix and also stored

- returns true when key is prefix and also stored
- Verify: returns true when key is prefix and also stored
   - Expected: t contains `app`
   - Expected: t contains `apple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when key is prefix and also stored")
step("Verify: returns true when key is prefix and also stored")
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
expect(t.contains("app")).to_equal(true)
expect(t.contains("apple")).to_equal(true)
```

</details>

### get_or

#### returns value for existing key

- returns value for existing key
- Verify: returns value for existing key
   - Expected: t.get_or("key", 99) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value for existing key")
step("Verify: returns value for existing key")
val t = PersistentTrie.empty().set("key", 10)
expect(t.get_or("key", 99)).to_equal(10)
```

</details>

#### returns default for missing key

- returns default for missing key
- Verify: returns default for missing key
   - Expected: t.get_or("key", 99) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default for missing key")
step("Verify: returns default for missing key")
val t = PersistentTrie.empty()
expect(t.get_or("key", 99)).to_equal(99)
```

</details>

#### returns default with text fallback

- returns default with text fallback
- Verify: returns default with text fallback
   - Expected: t.get_or("name", "unknown") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default with text fallback")
step("Verify: returns default with text fallback")
val t = PersistentTrie.empty()
expect(t.get_or("name", "unknown")).to_equal("unknown")
```

</details>

### persistence

#### preserves snapshots across multiple sets

- preserves snapshots across multiple sets
- Verify: preserves snapshots across multiple sets
   - Expected: t0.len() equals `0`
   - Expected: t1.len() equals `1`
   - Expected: t2.len() equals `2`
   - Expected: t3.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves snapshots across multiple sets")
step("Verify: preserves snapshots across multiple sets")
val t0 = PersistentTrie.empty()
val t1 = t0.set("a", 1)
val t2 = t1.set("b", 2)
val t3 = t2.set("c", 3)
expect(t0.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(t1.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(t2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(t3.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(t1.get("b")).to_be_nil()
expect(t2.get("c")).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

- overwrite does not affect earlier version
- Verify: overwrite does not affect earlier version
   - Expected: t1.get("key") equals `old`
   - Expected: t2.get("key") equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrite does not affect earlier version")
step("Verify: overwrite does not affect earlier version")
val t1 = PersistentTrie.empty().set("key", "old")
val t2 = t1.set("key", "new")
expect(t1.get("key")).to_equal("old")
expect(t2.get("key")).to_equal("new")
```

</details>

#### remove does not affect earlier version

- remove does not affect earlier version
- Verify: remove does not affect earlier version
   - Expected: t1.get("a") equals `1`
   - Expected: t1.len() equals `2`
   - Expected: t2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove does not affect earlier version")
step("Verify: remove does not affect earlier version")
val t1 = PersistentTrie.empty().set("a", 1).set("b", 2)
val t2 = t1.remove("a")
expect(t1.get("a")).to_equal(1)
expect(t1.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(t2.get("a")).to_be_nil()
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### remove

#### removes an existing key

- removes an existing key
- Verify: removes an existing key
   - Expected: t2.get("b") equals `2`
   - Expected: t2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes an existing key")
step("Verify: removes an existing key")
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val t2 = t.remove("a")
expect(t2.get("a")).to_be_nil()
expect(t2.get("b")).to_equal(2)
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### handles removing non-existent key

- handles removing non-existent key
- Verify: handles removing non-existent key
   - Expected: t2.len() equals `1`
   - Expected: t2.get("a") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles removing non-existent key")
step("Verify: handles removing non-existent key")
val t = PersistentTrie.empty().set("a", 1)
val t2 = t.remove("zzz")
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(t2.get("a")).to_equal(1)
```

</details>

#### removes last key to get empty trie

- removes last key to get empty trie
- Verify: removes last key to get empty trie
   - Expected: t2.len() equals `0`
   - Expected: t2.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes last key to get empty trie")
step("Verify: removes last key to get empty trie")
val t = PersistentTrie.empty().set("only", 99)
val t2 = t.remove("only")
expect(t2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(t2.is_empty()).to_equal(true)
```

</details>

#### removes prefix key but keeps longer key

- removes prefix key but keeps longer key
- Verify: removes prefix key but keeps longer key
   - Expected: t2.get("apple") equals `2`
   - Expected: t2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes prefix key but keeps longer key")
step("Verify: removes prefix key but keeps longer key")
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
val t2 = t.remove("app")
expect(t2.get("app")).to_be_nil()
expect(t2.get("apple")).to_equal(2)
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### removes longer key but keeps prefix key

- removes longer key but keeps prefix key
- Verify: removes longer key but keeps prefix key
   - Expected: t2.get("app") equals `1`
   - Expected: t2.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes longer key but keeps prefix key")
step("Verify: removes longer key but keeps prefix key")
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
val t2 = t.remove("apple")
expect(t2.get("apple")).to_be_nil()
expect(t2.get("app")).to_equal(1)
expect(t2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### removes from multi-key trie

- removes from multi-key trie
- Verify: removes from multi-key trie
   - Expected: t2.len() equals `2`
   - Expected: t2.get("a") equals `1`
   - Expected: t2.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes from multi-key trie")
step("Verify: removes from multi-key trie")
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val t2 = t.remove("b")
expect(t2.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(t2.get("a")).to_equal(1)
expect(t2.get("b")).to_be_nil()
expect(t2.get("c")).to_equal(3)
```

</details>

### keys_with_prefix

#### finds all keys starting with prefix

- finds all keys starting with prefix
- Verify: finds all keys starting with prefix
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds all keys starting with prefix")
step("Verify: finds all keys starting with prefix")
val t = PersistentTrie.empty().set("app", 1).set("apple", 2).set("application", 3).set("banana", 4)
val result = t.keys_with_prefix("app")
expect(result.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result).to_contain("app")
expect(result).to_contain("apple")
expect(result).to_contain("application")
```

</details>

#### returns empty for non-matching prefix

- returns empty for non-matching prefix
- Verify: returns empty for non-matching prefix
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for non-matching prefix")
step("Verify: returns empty for non-matching prefix")
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2)
val result = t.keys_with_prefix("xyz")
expect(result.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### returns exact match when prefix is a key

- returns exact match when prefix is a key
- Verify: returns exact match when prefix is a key
   - Expected: result.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exact match when prefix is a key")
step("Verify: returns exact match when prefix is a key")
val t = PersistentTrie.empty().set("test", 1)
val result = t.keys_with_prefix("test")
expect(result.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result).to_contain("test")
```

</details>

#### returns all keys for empty prefix

- returns all keys for empty prefix
- Verify: returns all keys for empty prefix
   - Expected: result.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all keys for empty prefix")
step("Verify: returns all keys for empty prefix")
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val result = t.keys_with_prefix("")
expect(result.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### single character prefix

- single character prefix
- Verify: single character prefix
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single character prefix")
step("Verify: single character prefix")
val t = PersistentTrie.empty().set("cat", 1).set("car", 2).set("dog", 3)
val result = t.keys_with_prefix("ca")
expect(result.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result).to_contain("cat")
expect(result).to_contain("car")
```

</details>

### longest_prefix

#### finds the longest key that is a prefix of query

- finds the longest key that is a prefix of query
- Verify: finds the longest key that is a prefix of query
   - Expected: result equals `apple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds the longest key that is a prefix of query")
step("Verify: finds the longest key that is a prefix of query")
val t = PersistentTrie.empty().set("a", 1).set("app", 2).set("apple", 3)
val result = t.longest_prefix("applesauce")
expect(result).to_equal("apple")
```

</details>

#### returns shorter prefix when exact match not present

- returns shorter prefix when exact match not present
- Verify: returns shorter prefix when exact match not present
   - Expected: result equals `app`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns shorter prefix when exact match not present")
step("Verify: returns shorter prefix when exact match not present")
val t = PersistentTrie.empty().set("a", 1).set("app", 2)
val result = t.longest_prefix("application")
expect(result).to_equal("app")
```

</details>

#### returns nil when no key is a prefix

- returns nil when no key is a prefix
- Verify: returns nil when no key is a prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when no key is a prefix")
step("Verify: returns nil when no key is a prefix")
val t = PersistentTrie.empty().set("xyz", 1)
val result = t.longest_prefix("abc")
expect(result).to_be_nil()
```

</details>

#### returns exact match when query equals a key

- returns exact match when query equals a key
- Verify: returns exact match when query equals a key
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exact match when query equals a key")
step("Verify: returns exact match when query equals a key")
val t = PersistentTrie.empty().set("hello", 1)
val result = t.longest_prefix("hello")
expect(result).to_equal("hello")
```

</details>

#### returns single char prefix

- returns single char prefix
- Verify: returns single char prefix
   - Expected: result equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single char prefix")
step("Verify: returns single char prefix")
val t = PersistentTrie.empty().set("h", 1)
val result = t.longest_prefix("hello")
expect(result).to_equal("h")
```

</details>

### iteration

#### keys returns all stored keys

- keys returns all stored keys
- Verify: keys returns all stored keys
   - Expected: k.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys returns all stored keys")
step("Verify: keys returns all stored keys")
val t = PersistentTrie.empty().set("b", 2).set("a", 1).set("c", 3)
val k = t.keys()
expect(k.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### values returns all stored values

- values returns all stored values
- Verify: values returns all stored values
   - Expected: v.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values returns all stored values")
step("Verify: values returns all stored values")
val t = PersistentTrie.empty().set("x", 10).set("y", 20)
val v = t.values()
expect(v.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### entries returns key-value pairs

- entries returns key-value pairs
- Verify: entries returns key-value pairs
   - Expected: e.len() equals `1`
   - Expected: pair[0] equals `a`
   - Expected: pair[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries returns key-value pairs")
step("Verify: entries returns key-value pairs")
val t = PersistentTrie.empty().set("a", 1)
val e = t.entries()
expect(e.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val pair = e[0]
expect(pair[0]).to_equal("a")
expect(pair[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### entries returns correct count for multi-entry trie

- entries returns correct count for multi-entry trie
- Verify: entries returns correct count for multi-entry trie
   - Expected: e.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("entries returns correct count for multi-entry trie")
step("Verify: entries returns correct count for multi-entry trie")
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val e = t.entries()
expect(e.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val filtered = t.filter(fn(k, v): v > 1)
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 100)
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### filter by key

- filter by key
- Verify: filter by key
   - Expected: filtered.len() equals `1`
   - Expected: filtered.get("apple") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filter by key")
step("Verify: filter by key")
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2).set("avocado", 3)
val filtered = t.filter(fn(k, v): k == "apple")
expect(filtered.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(filtered.get("apple")).to_equal(1)
```

</details>

#### does not modify original

- does not modify original
- Verify: does not modify original
   - Expected: t.len() equals `2`
   - Expected: filtered.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not modify original")
step("Verify: does not modify original")
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 1)
expect(t.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
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
# @req REQ-SSPEC-UNIT
step("sums all values")
step("Verify: sums all values")
val t = PersistentTrie.empty().set("a", 10).set("b", 20).set("c", 30)
val total = t.fold(0, fn(acc, k, v): acc + v)
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
# @req REQ-SSPEC-UNIT
step("fold over empty returns init")
step("Verify: fold over empty returns init")
val t = PersistentTrie.empty()
val result = t.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)  # oracle: 42 — named expected value from the requirement
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
# @req REQ-SSPEC-UNIT
step("fold counts entries")
step("Verify: fold counts entries")
val t = PersistentTrie.empty().set("x", 1).set("y", 2).set("z", 3)
val count = t.fold(0, fn(acc, k, v): acc + 1)
expect(count).to_equal(3)  # oracle: 3 — named expected value from the requirement
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val doubled = t.map_values(fn(v): v * 2)
expect(doubled.get("a")).to_equal(2)
expect(doubled.get("b")).to_equal(4)
expect(doubled.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### does not modify original

- does not modify original
- Verify: does not modify original
   - Expected: t.get("a") equals `5`
   - Expected: mapped.get("a") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not modify original")
step("Verify: does not modify original")
val t = PersistentTrie.empty().set("a", 5)
val mapped = t.map_values(fn(v): v + 10)
expect(t.get("a")).to_equal(5)
expect(mapped.get("a")).to_equal(15)
```

</details>

#### maps to different type

- maps to different type
- Verify: maps to different type
   - Expected: mapped.get("x") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps to different type")
step("Verify: maps to different type")
val t = PersistentTrie.empty().set("x", 3)
val mapped = t.map_values(fn(v): v * v)
expect(mapped.get("x")).to_equal(9)
```

</details>

### update

#### updates existing key

- updates existing key
- Verify: updates existing key
   - Expected: t2.get("count") equals `6`
   - Expected: t.get("count") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates existing key")
step("Verify: updates existing key")
val t = PersistentTrie.empty().set("count", 5)
val t2 = t.update("count", fn(v): v + 1)
expect(t2.get("count")).to_equal(6)
expect(t.get("count")).to_equal(5)
```

</details>

#### creates key when missing

- creates key when missing
- Verify: creates key when missing
   - Expected: t2.get("new") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates key when missing")
step("Verify: creates key when missing")
val t = PersistentTrie.empty()
val t2 = t.update("new", fn(v): 42)
expect(t2.get("new")).to_equal(42)
```

</details>

### from_entries

#### builds from key-value pairs

- builds from key-value pairs
- Verify: builds from key-value pairs
   - Expected: t.get("a") equals `1`
   - Expected: t.get("b") equals `2`
   - Expected: t.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds from key-value pairs")
step("Verify: builds from key-value pairs")
val t = PersistentTrie.from_entries([["a", 1], ["b", 2]])
expect(t.get("a")).to_equal(1)
expect(t.get("b")).to_equal(2)
expect(t.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles empty entries

- handles empty entries
- Verify: handles empty entries
   - Expected: t.len() equals `0`
   - Expected: t.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty entries")
step("Verify: handles empty entries")
val t = PersistentTrie.from_entries([])
expect(t.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(t.is_empty()).to_equal(true)
```

</details>

#### handles single entry

- handles single entry
- Verify: handles single entry
   - Expected: t.get("only") equals `99`
   - Expected: t.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single entry")
step("Verify: handles single entry")
val t = PersistentTrie.from_entries([["only", 99]])
expect(t.get("only")).to_equal(99)
expect(t.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### last value wins for duplicate keys

- last value wins for duplicate keys
- Verify: last value wins for duplicate keys
   - Expected: t.get("a") equals `2`
   - Expected: t.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last value wins for duplicate keys")
step("Verify: last value wins for duplicate keys")
val t = PersistentTrie.from_entries([["a", 1], ["a", 2]])
expect(t.get("a")).to_equal(2)
expect(t.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### from_dict

#### builds from mutable dict

- builds from mutable dict
- Verify: builds from mutable dict
   - Expected: t.get("x") equals `10`
   - Expected: t.get("y") equals `20`
   - Expected: t.len() equals `2`


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
val t = PersistentTrie.from_dict(d)
expect(t.get("x")).to_equal(10)
expect(t.get("y")).to_equal(20)
expect(t.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### handles empty dict

- handles empty dict
- Verify: handles empty dict
   - Expected: t.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty dict")
step("Verify: handles empty dict")
val d = {}
val t = PersistentTrie.from_dict(d)
expect(t.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
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
val t = PersistentTrie.empty().set("x", 10).set("y", 20)
val d = t.to_dict()
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
```

</details>

#### empty trie converts to empty dict

- empty trie converts to empty dict
- Verify: empty trie converts to empty dict
   - Expected: d.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty trie converts to empty dict")
step("Verify: empty trie converts to empty dict")
val t = PersistentTrie.empty()
val d = t.to_dict()
expect(d.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### copy

#### returns identical trie

- returns identical trie
- Verify: returns identical trie
   - Expected: c.get("a") equals `1`
   - Expected: c.get("b") equals `2`
   - Expected: c.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns identical trie")
step("Verify: returns identical trie")
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val c = t.copy()
expect(c.get("a")).to_equal(1)
expect(c.get("b")).to_equal(2)
expect(c.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
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
# @req REQ-SSPEC-UNIT
step("handles many insertions via helper fn")
step("Verify: handles many insertions via helper fn")
fn run_insert_stress() -> i64:
    var t = PersistentTrie.empty()
    var i = 0
    while i < 100:
        t = t.set("key_{i}", i)
        i = i + 1
    t.len()
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
# @req REQ-SSPEC-UNIT
step("set and get many elements")
step("Verify: set and get many elements")
fn run_get_stress() -> i64:
    var t = PersistentTrie.empty()
    var i = 0
    while i < 50:
        t = t.set("k_{i}", i * 10)
        i = i + 1
    var ok_count = 0
    i = 0
    while i < 50:
        val v = t.get("k_{i}")
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
    var t = PersistentTrie.empty()
    var i = 0
    while i < 30:
        t = t.set("r_{i}", i)
        i = i + 1
    i = 0
    while i < 15:
        t = t.remove("r_{i}")
        i = i + 1
    t.len()
expect(run_remove_stress()).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

### edge cases

#### empty string key

- empty string key
- Verify: empty string key
   - Expected: t.get("") equals `empty_key`
   - Expected: t.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string key")
step("Verify: empty string key")
val t = PersistentTrie.empty().set("", "empty_key")
expect(t.get("")).to_equal("empty_key")
expect(t.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### single character keys

- single character keys
- Verify: single character keys
   - Expected: t.get("a") equals `1`
   - Expected: t.get("b") equals `2`
   - Expected: t.get("c") equals `3`
   - Expected: t.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single character keys")
step("Verify: single character keys")
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
expect(t.get("a")).to_equal(1)
expect(t.get("b")).to_equal(2)
expect(t.get("c")).to_equal(3)
expect(t.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### keys that share no prefix

- keys that share no prefix
- Verify: keys that share no prefix
   - Expected: t.get("xyz") equals `1`
   - Expected: t.get("abc") equals `2`
   - Expected: t.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys that share no prefix")
step("Verify: keys that share no prefix")
val t = PersistentTrie.empty().set("xyz", 1).set("abc", 2)
expect(t.get("xyz")).to_equal(1)
expect(t.get("abc")).to_equal(2)
expect(t.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### deeply nested keys

- deeply nested keys
- Verify: deeply nested keys
   - Expected: t.get("abcdefghij") equals `1`
   - Expected: t.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deeply nested keys")
step("Verify: deeply nested keys")
val t = PersistentTrie.empty().set("abcdefghij", 1)
expect(t.get("abcdefghij")).to_equal(1)
expect(t.get("abcde")).to_be_nil()
expect(t.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### prefix operations with shared prefixes

- prefix operations with shared prefixes
- Verify: prefix operations with shared prefixes
   - Expected: prefix_keys.len() equals `3`
   - Expected: longest equals `abcde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefix operations with shared prefixes")
step("Verify: prefix operations with shared prefixes")
val t = PersistentTrie.empty().set("ab", 1).set("abc", 2).set("abcd", 3).set("abcde", 4)
val prefix_keys = t.keys_with_prefix("abc")
expect(prefix_keys.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(prefix_keys).to_contain("abc")
expect(prefix_keys).to_contain("abcd")
expect(prefix_keys).to_contain("abcde")
val longest = t.longest_prefix("abcdef")
expect(longest).to_equal("abcde")
```

</details>

#### remove from empty trie returns same trie

- remove from empty trie returns same trie
- Verify: remove from empty trie returns same trie
   - Expected: t2.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove from empty trie returns same trie")
step("Verify: remove from empty trie returns same trie")
val t = PersistentTrie.empty()
val t2 = t.remove("nothing")
expect(t2.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
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

- Canonical SPipe generation for source `3786474fd3c611eff078d3d761edffc921d35598c9242ecd3a21b621c15994f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3786474fd3c611eff078d3d761edffc921d35598c9242ecd3a21b621c15994f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3786474fd3c611eff078d3d761edffc921d35598c9242ecd3a21b621c15994f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/immut/persistent_trie_spec.spl
mirror: doc/06_spec/unit/lib/common/immut/persistent_trie_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/immut/persistent_trie_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/immut/persistent_trie_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/immut/persistent_trie_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 46 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/immut/persistent_trie_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has zero length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_trie_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_trie_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get returns nil for any key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
