# Persistent Trie Specification

> <details>

<!-- sdn-diagram:id=persistent_trie_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_trie_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_trie_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_trie_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Trie Specification

## Scenarios

### PersistentTrie

### empty trie

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.is_empty()).to_equal(true)
```

</details>

#### get returns nil for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.get("hello")).to_be_nil()
expect(t.get("")).to_be_nil()
```

</details>

#### get_or returns default for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.get_or("hello", 42)).to_equal(42)
```

</details>

#### contains returns false for any key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.contains("hello")).to_equal(false)
```

</details>

#### keys returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.keys().len()).to_equal(0)
```

</details>

#### values returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.values().len()).to_equal(0)
```

</details>

#### entries returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.entries().len()).to_equal(0)
```

</details>

#### keys_with_prefix returns empty on empty trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.keys_with_prefix("any").len()).to_equal(0)
```

</details>

#### longest_prefix returns nil on empty trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.longest_prefix("anything")).to_be_nil()
```

</details>

### set and get

#### stores and retrieves a single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1)
expect(t.get("hello")).to_equal(1)
expect(t.len()).to_equal(1)
```

</details>

#### returns new trie on set - original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = PersistentTrie.empty()
val t2 = t1.set("key", 42)
expect(t1.len()).to_equal(0)
expect(t1.get("key")).to_be_nil()
expect(t2.len()).to_equal(1)
expect(t2.get("key")).to_equal(42)
```

</details>

#### overwrites existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = PersistentTrie.empty().set("key", "old")
val t2 = t1.set("key", "new")
expect(t2.get("key")).to_equal("new")
expect(t2.len()).to_equal(1)
```

</details>

#### handles two keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2)
expect(t.get("apple")).to_equal(1)
expect(t.get("banana")).to_equal(2)
expect(t.len()).to_equal(2)
```

</details>

#### handles keys sharing prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("app", 1).set("apple", 2).set("application", 3)
expect(t.get("app")).to_equal(1)
expect(t.get("apple")).to_equal(2)
expect(t.get("application")).to_equal(3)
expect(t.len()).to_equal(3)
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1)
expect(t.get("world")).to_be_nil()
```

</details>

#### returns nil for partial prefix key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("apple", 1)
expect(t.get("app")).to_be_nil()
```

</details>

#### is no longer empty after set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("x", 1)
expect(t.is_empty()).to_equal(false)
```

</details>

#### stores integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("count", 42)
expect(t.get("count")).to_equal(42)
```

</details>

#### stores text values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("name", "Alice")
expect(t.get("name")).to_equal("Alice")
```

</details>

### contains

#### returns true for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1)
expect(t.contains("hello")).to_equal(true)
```

</details>

#### returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1)
expect(t.contains("world")).to_equal(false)
```

</details>

#### returns false for prefix of existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("apple", 1)
expect(t.contains("app")).to_equal(false)
```

</details>

#### returns false after removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1).remove("hello")
expect(t.contains("hello")).to_equal(false)
```

</details>

#### returns true when key is prefix and also stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
expect(t.contains("app")).to_equal(true)
expect(t.contains("apple")).to_equal(true)
```

</details>

### get_or

#### returns value for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("key", 10)
expect(t.get_or("key", 99)).to_equal(10)
```

</details>

#### returns default for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.get_or("key", 99)).to_equal(99)
```

</details>

#### returns default with text fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
expect(t.get_or("name", "unknown")).to_equal("unknown")
```

</details>

### persistence

#### preserves snapshots across multiple sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = PersistentTrie.empty()
val t1 = t0.set("a", 1)
val t2 = t1.set("b", 2)
val t3 = t2.set("c", 3)
expect(t0.len()).to_equal(0)
expect(t1.len()).to_equal(1)
expect(t2.len()).to_equal(2)
expect(t3.len()).to_equal(3)
expect(t1.get("b")).to_be_nil()
expect(t2.get("c")).to_be_nil()
```

</details>

#### overwrite does not affect earlier version

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = PersistentTrie.empty().set("key", "old")
val t2 = t1.set("key", "new")
expect(t1.get("key")).to_equal("old")
expect(t2.get("key")).to_equal("new")
```

</details>

#### remove does not affect earlier version

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = PersistentTrie.empty().set("a", 1).set("b", 2)
val t2 = t1.remove("a")
expect(t1.get("a")).to_equal(1)
expect(t1.len()).to_equal(2)
expect(t2.get("a")).to_be_nil()
expect(t2.len()).to_equal(1)
```

</details>

### remove

#### removes an existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val t2 = t.remove("a")
expect(t2.get("a")).to_be_nil()
expect(t2.get("b")).to_equal(2)
expect(t2.len()).to_equal(1)
```

</details>

#### handles removing non-existent key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1)
val t2 = t.remove("zzz")
expect(t2.len()).to_equal(1)
expect(t2.get("a")).to_equal(1)
```

</details>

#### removes last key to get empty trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("only", 99)
val t2 = t.remove("only")
expect(t2.len()).to_equal(0)
expect(t2.is_empty()).to_equal(true)
```

</details>

#### removes prefix key but keeps longer key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
val t2 = t.remove("app")
expect(t2.get("app")).to_be_nil()
expect(t2.get("apple")).to_equal(2)
expect(t2.len()).to_equal(1)
```

</details>

#### removes longer key but keeps prefix key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("app", 1).set("apple", 2)
val t2 = t.remove("apple")
expect(t2.get("apple")).to_be_nil()
expect(t2.get("app")).to_equal(1)
expect(t2.len()).to_equal(1)
```

</details>

#### removes from multi-key trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val t2 = t.remove("b")
expect(t2.len()).to_equal(2)
expect(t2.get("a")).to_equal(1)
expect(t2.get("b")).to_be_nil()
expect(t2.get("c")).to_equal(3)
```

</details>

### keys_with_prefix

#### finds all keys starting with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("app", 1).set("apple", 2).set("application", 3).set("banana", 4)
val result = t.keys_with_prefix("app")
expect(result.len()).to_equal(3)
expect(result).to_contain("app")
expect(result).to_contain("apple")
expect(result).to_contain("application")
```

</details>

#### returns empty for non-matching prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2)
val result = t.keys_with_prefix("xyz")
expect(result.len()).to_equal(0)
```

</details>

#### returns exact match when prefix is a key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("test", 1)
val result = t.keys_with_prefix("test")
expect(result.len()).to_equal(1)
expect(result).to_contain("test")
```

</details>

#### returns all keys for empty prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val result = t.keys_with_prefix("")
expect(result.len()).to_equal(3)
```

</details>

#### single character prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("cat", 1).set("car", 2).set("dog", 3)
val result = t.keys_with_prefix("ca")
expect(result.len()).to_equal(2)
expect(result).to_contain("cat")
expect(result).to_contain("car")
```

</details>

### longest_prefix

#### finds the longest key that is a prefix of query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("app", 2).set("apple", 3)
val result = t.longest_prefix("applesauce")
expect(result).to_equal("apple")
```

</details>

#### returns shorter prefix when exact match not present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("app", 2)
val result = t.longest_prefix("application")
expect(result).to_equal("app")
```

</details>

#### returns nil when no key is a prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("xyz", 1)
val result = t.longest_prefix("abc")
expect(result).to_be_nil()
```

</details>

#### returns exact match when query equals a key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("hello", 1)
val result = t.longest_prefix("hello")
expect(result).to_equal("hello")
```

</details>

#### returns single char prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("h", 1)
val result = t.longest_prefix("hello")
expect(result).to_equal("h")
```

</details>

### iteration

#### keys returns all stored keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("b", 2).set("a", 1).set("c", 3)
val k = t.keys()
expect(k.len()).to_equal(3)
```

</details>

#### values returns all stored values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("x", 10).set("y", 20)
val v = t.values()
expect(v.len()).to_equal(2)
```

</details>

#### entries returns key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1)
val e = t.entries()
expect(e.len()).to_equal(1)
val pair = e[0]
expect(pair[0]).to_equal("a")
expect(pair[1]).to_equal(1)
```

</details>

#### entries returns correct count for multi-entry trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val e = t.entries()
expect(e.len()).to_equal(3)
```

</details>

### filter

#### keeps entries matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
val filtered = t.filter(fn(k, v): v > 1)
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 100)
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
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 0)
expect(filtered.len()).to_equal(2)
```

</details>

#### filter by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("apple", 1).set("banana", 2).set("avocado", 3)
val filtered = t.filter(fn(k, v): k == "apple")
expect(filtered.len()).to_equal(1)
expect(filtered.get("apple")).to_equal(1)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val filtered = t.filter(fn(k, v): v > 1)
expect(t.len()).to_equal(2)
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
val t = PersistentTrie.empty().set("a", 10).set("b", 20).set("c", 30)
val total = t.fold(0, fn(acc, k, v): acc + v)
expect(total).to_equal(60)
```

</details>

#### fold over empty returns init

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
val result = t.fold(42, fn(acc, k, v): acc + v)
expect(result).to_equal(42)
```

</details>

#### fold counts entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("x", 1).set("y", 2).set("z", 3)
val count = t.fold(0, fn(acc, k, v): acc + 1)
expect(count).to_equal(3)
```

</details>

### map_values

#### transforms all values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val doubled = t.map_values(fn(v): v * 2)
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
val t = PersistentTrie.empty().set("a", 5)
val mapped = t.map_values(fn(v): v + 10)
expect(t.get("a")).to_equal(5)
expect(mapped.get("a")).to_equal(15)
```

</details>

#### maps to different type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("x", 3)
val mapped = t.map_values(fn(v): v * v)
expect(mapped.get("x")).to_equal(9)
```

</details>

### update

#### updates existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("count", 5)
val t2 = t.update("count", fn(v): v + 1)
expect(t2.get("count")).to_equal(6)
expect(t.get("count")).to_equal(5)
```

</details>

#### creates key when missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
val t2 = t.update("new", fn(v): 42)
expect(t2.get("new")).to_equal(42)
```

</details>

### from_entries

#### builds from key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.from_entries([["a", 1], ["b", 2]])
expect(t.get("a")).to_equal(1)
expect(t.get("b")).to_equal(2)
expect(t.len()).to_equal(2)
```

</details>

#### handles empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.from_entries([])
expect(t.len()).to_equal(0)
expect(t.is_empty()).to_equal(true)
```

</details>

#### handles single entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.from_entries([["only", 99]])
expect(t.get("only")).to_equal(99)
expect(t.len()).to_equal(1)
```

</details>

#### last value wins for duplicate keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.from_entries([["a", 1], ["a", 2]])
expect(t.get("a")).to_equal(2)
expect(t.len()).to_equal(1)
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
val t = PersistentTrie.from_dict(d)
expect(t.get("x")).to_equal(10)
expect(t.get("y")).to_equal(20)
expect(t.len()).to_equal(2)
```

</details>

#### handles empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {}
val t = PersistentTrie.from_dict(d)
expect(t.len()).to_equal(0)
```

</details>

### to_dict

#### converts to mutable dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("x", 10).set("y", 20)
val d = t.to_dict()
expect(d["x"]).to_equal(10)
expect(d["y"]).to_equal(20)
```

</details>

#### empty trie converts to empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
val d = t.to_dict()
expect(d.len()).to_equal(0)
```

</details>

### copy

#### returns identical trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2)
val c = t.copy()
expect(c.get("a")).to_equal(1)
expect(c.get("b")).to_equal(2)
expect(c.len()).to_equal(2)
```

</details>

### stress test

#### handles many insertions via helper fn

- fn run insert stress
- var t = PersistentTrie empty
- t = t set
- t len
   - Expected: run_insert_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_insert_stress() -> i64:
    var t = PersistentTrie.empty()
    var i = 0
    while i < 100:
        t = t.set("key_{i}", i)
        i = i + 1
    t.len()
expect(run_insert_stress()).to_equal(100)
```

</details>

#### set and get many elements

- fn run get stress
- var t = PersistentTrie empty
- t = t set
   - Expected: run_get_stress() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(run_get_stress()).to_equal(50)
```

</details>

#### remove many elements

- fn run remove stress
- var t = PersistentTrie empty
- t = t set
- t = t remove
- t len
   - Expected: run_remove_stress() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(run_remove_stress()).to_equal(15)
```

</details>

### edge cases

#### empty string key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("", "empty_key")
expect(t.get("")).to_equal("empty_key")
expect(t.len()).to_equal(1)
```

</details>

#### single character keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("a", 1).set("b", 2).set("c", 3)
expect(t.get("a")).to_equal(1)
expect(t.get("b")).to_equal(2)
expect(t.get("c")).to_equal(3)
expect(t.len()).to_equal(3)
```

</details>

#### keys that share no prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("xyz", 1).set("abc", 2)
expect(t.get("xyz")).to_equal(1)
expect(t.get("abc")).to_equal(2)
expect(t.len()).to_equal(2)
```

</details>

#### deeply nested keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("abcdefghij", 1)
expect(t.get("abcdefghij")).to_equal(1)
expect(t.get("abcde")).to_be_nil()
expect(t.len()).to_equal(1)
```

</details>

#### prefix operations with shared prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty().set("ab", 1).set("abc", 2).set("abcd", 3).set("abcde", 4)
val prefix_keys = t.keys_with_prefix("abc")
expect(prefix_keys.len()).to_equal(3)
expect(prefix_keys).to_contain("abc")
expect(prefix_keys).to_contain("abcd")
expect(prefix_keys).to_contain("abcde")
val longest = t.longest_prefix("abcdef")
expect(longest).to_equal("abcde")
```

</details>

#### remove from empty trie returns same trie

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = PersistentTrie.empty()
val t2 = t.remove("nothing")
expect(t2.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_trie_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentTrie
- empty trie
- set and get
- contains
- get_or
- persistence
- remove
- keys_with_prefix
- longest_prefix
- iteration
- filter
- fold
- map_values
- update
- from_entries
- from_dict
- to_dict
- copy
- stress test
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
