# Persistent Builder Specification

> <details>

<!-- sdn-diagram:id=persistent_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_builder_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Builder Specification

## Scenarios

### PersistentVecBuilder

### creation

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.new()
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

#### starts not frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.new()
expect(b.is_frozen()).to_equal(false)
```

</details>

### from factory

#### pre-populates with items

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([10, 20, 30])
expect(b.len()).to_equal(3)
expect(b.get(0)).to_equal(10)
expect(b.get(2)).to_equal(30)
```

</details>

#### is not frozen after creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([1, 2])
expect(b.is_frozen()).to_equal(false)
```

</details>

#### empty array gives empty builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([])
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

### push

#### adds single element

- var b = PersistentVecBuilder new
- b push
   - Expected: b.len() equals `1`
   - Expected: b.get(0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(42)
expect(b.len()).to_equal(1)
expect(b.get(0)).to_equal(42)
```

</details>

#### adds multiple elements in order

- var b = PersistentVecBuilder new
- b push
- b push
- b push
   - Expected: b.len() equals `3`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.push(3)
expect(b.len()).to_equal(3)
expect(b.get(0)).to_equal(1)
expect(b.get(1)).to_equal(2)
expect(b.get(2)).to_equal(3)
```

</details>

#### is no longer empty after push

- var b = PersistentVecBuilder new
- b push
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(99)
expect(b.is_empty()).to_equal(false)
```

</details>

### push_all

#### adds all items from array

- var b = PersistentVecBuilder new
- b push all
   - Expected: b.len() equals `3`
   - Expected: b.get(0) equals `10`
   - Expected: b.get(2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push_all([10, 20, 30])
expect(b.len()).to_equal(3)
expect(b.get(0)).to_equal(10)
expect(b.get(2)).to_equal(30)
```

</details>

#### appends to existing items

- var b = PersistentVecBuilder new
- b push
- b push all
   - Expected: b.len() equals `4`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(3) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.push_all([2, 3, 4])
expect(b.len()).to_equal(4)
expect(b.get(0)).to_equal(1)
expect(b.get(3)).to_equal(4)
```

</details>

#### empty array is no-op

- var b = PersistentVecBuilder new
- b push
- b push all
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.push_all([])
expect(b.len()).to_equal(1)
```

</details>

### set_at

#### replaces element at index

- var b = PersistentVecBuilder from
- b set at
   - Expected: b.get(1) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([10, 20, 30])
b.set_at(1, 99)
expect(b.get(1)).to_equal(99)
```

</details>

#### preserves other elements

- var b = PersistentVecBuilder from
- b set at
   - Expected: b.get(0) equals `99`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2, 3])
b.set_at(0, 99)
expect(b.get(0)).to_equal(99)
expect(b.get(1)).to_equal(2)
expect(b.get(2)).to_equal(3)
```

</details>

#### ignores negative index

- var b = PersistentVecBuilder from
- b set at
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2, 3])
b.set_at(-1, 99)
expect(b.get(0)).to_equal(1)
expect(b.get(1)).to_equal(2)
expect(b.get(2)).to_equal(3)
```

</details>

#### ignores out of bounds index

- var b = PersistentVecBuilder from
- b set at
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2])
b.set_at(10, 99)
expect(b.len()).to_equal(2)
```

</details>

### pop

#### removes last element

- var b = PersistentVecBuilder from
- b pop
   - Expected: b.len() equals `2`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2, 3])
b.pop()
expect(b.len()).to_equal(2)
expect(b.get(0)).to_equal(1)
expect(b.get(1)).to_equal(2)
```

</details>

### clear

#### removes all elements

- var b = PersistentVecBuilder from
- b clear
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2, 3])
b.clear()
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

#### allows push after clear

- var b = PersistentVecBuilder from
- b clear
- b push
   - Expected: b.len() equals `1`
   - Expected: b.get(0) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2])
b.clear()
b.push(99)
expect(b.len()).to_equal(1)
expect(b.get(0)).to_equal(99)
```

</details>

### get

#### returns element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([10, 20, 30])
expect(b.get(0)).to_equal(10)
expect(b.get(1)).to_equal(20)
expect(b.get(2)).to_equal(30)
```

</details>

#### returns nil for out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([1, 2])
expect(b.get(5)).to_be_nil()
```

</details>

#### returns nil for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.from([1, 2])
expect(b.get(-1)).to_be_nil()
```

</details>

### to_array

#### returns copy of items

- var b = PersistentVecBuilder new
- b push
- b push
- b push
   - Expected: arr.len() equals `3`
   - Expected: arr[0] equals `1`
   - Expected: arr[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.push(3)
val arr = b.to_array()
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(1)
expect(arr[2]).to_equal(3)
```

</details>

#### empty builder returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentVecBuilder.new()
val arr = b.to_array()
expect(arr.len()).to_equal(0)
```

</details>

### build and freeze

#### returns items as array

- var b = PersistentVecBuilder new
- b push
- b push
- b push
   - Expected: items.len() equals `3`
   - Expected: items[0] equals `10`
   - Expected: items[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(10)
b.push(20)
b.push(30)
val items = b.build()
expect(items.len()).to_equal(3)
expect(items[0]).to_equal(10)
expect(items[2]).to_equal(30)
```

</details>

#### marks builder as frozen

- var b = PersistentVecBuilder new
- b push
- b build
   - Expected: b.is_frozen() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.build()
expect(b.is_frozen()).to_equal(true)
```

</details>

#### push is no-op after freeze

- var b = PersistentVecBuilder new
- b push
- b push
- b build
- b push
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.build()
b.push(3)
expect(b.len()).to_equal(2)
```

</details>

#### push_all is no-op after freeze

- var b = PersistentVecBuilder new
- b push
- b build
- b push all
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(1)
b.build()
b.push_all([2, 3, 4])
expect(b.len()).to_equal(1)
```

</details>

#### set_at is no-op after freeze

- var b = PersistentVecBuilder from
- b build
- b set at
   - Expected: b.get(0) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([10, 20])
b.build()
b.set_at(0, 99)
expect(b.get(0)).to_equal(10)
```

</details>

#### clear is no-op after freeze

- var b = PersistentVecBuilder from
- b build
- b clear
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.from([1, 2, 3])
b.build()
b.clear()
expect(b.len()).to_equal(3)
```

</details>

#### reads still work after freeze

- var b = PersistentVecBuilder new
- b push
- b push
- b build
   - Expected: b.len() equals `2`
   - Expected: b.get(0) equals `10`
   - Expected: b.get(1) equals `20`
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentVecBuilder.new()
b.push(10)
b.push(20)
b.build()
expect(b.len()).to_equal(2)
expect(b.get(0)).to_equal(10)
expect(b.get(1)).to_equal(20)
expect(b.is_empty()).to_equal(false)
```

</details>

### PersistentMapBuilder

### creation

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

#### starts not frozen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
expect(b.is_frozen()).to_equal(false)
```

</details>

### from_entries factory

#### pre-populates with entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.from_entries([["a", 1], ["b", 2]])
expect(b.len()).to_equal(2)
expect(b.get("a")).to_equal(1)
expect(b.get("b")).to_equal(2)
```

</details>

#### is not frozen after creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.from_entries([["x", 10]])
expect(b.is_frozen()).to_equal(false)
```

</details>

#### empty entries gives empty builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.from_entries([])
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

#### handles duplicate keys in entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.from_entries([["a", 1], ["a", 2]])
expect(b.len()).to_equal(1)
expect(b.get("a")).to_equal(2)
```

</details>

### set and get

#### stores and retrieves a value

- var b = PersistentMapBuilder new
- b set
   - Expected: b.get("name") equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("name", "Alice")
expect(b.get("name")).to_equal("Alice")
```

</details>

#### stores multiple key-value pairs

- var b = PersistentMapBuilder new
- b set
- b set
- b set
   - Expected: b.len() equals `3`
   - Expected: b.get("a") equals `1`
   - Expected: b.get("b") equals `2`
   - Expected: b.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.set("c", 3)
expect(b.len()).to_equal(3)
expect(b.get("a")).to_equal(1)
expect(b.get("b")).to_equal(2)
expect(b.get("c")).to_equal(3)
```

</details>

#### overwrites existing key

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: b.get("key") equals `new`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("key", "old")
b.set("key", "new")
expect(b.get("key")).to_equal("new")
expect(b.len()).to_equal(1)
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
expect(b.get("nothing")).to_be_nil()
```

</details>

#### stores integer keys

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: b.get(1) equals `one`
   - Expected: b.get(2) equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set(1, "one")
b.set(2, "two")
expect(b.get(1)).to_equal("one")
expect(b.get(2)).to_equal("two")
```

</details>

### set_all

#### adds multiple entries

- var b = PersistentMapBuilder new
- b set all
   - Expected: b.len() equals `3`
   - Expected: b.get("x") equals `10`
   - Expected: b.get("z") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set_all([["x", 10], ["y", 20], ["z", 30]])
expect(b.len()).to_equal(3)
expect(b.get("x")).to_equal(10)
expect(b.get("z")).to_equal(30)
```

</details>

#### appends to existing entries

- var b = PersistentMapBuilder new
- b set
- b set all
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set_all([["b", 2], ["c", 3]])
expect(b.len()).to_equal(3)
```

</details>

### contains

#### returns true for existing key

- var b = PersistentMapBuilder new
- b set
   - Expected: b contains `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 42)
expect(b.contains("x")).to_equal(true)
```

</details>

#### returns false for missing key

- var b = PersistentMapBuilder new
- b set
   - Expected: b does not contain `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 42)
expect(b.contains("y")).to_equal(false)
```

</details>

#### returns false for empty builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
expect(b.contains("anything")).to_equal(false)
```

</details>

### remove

#### removes an existing key

- var b = PersistentMapBuilder new
- b set
- b set
- b remove
   - Expected: b does not contain `a`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.remove("a")
expect(b.get("a")).to_be_nil()
expect(b.contains("a")).to_equal(false)
expect(b.len()).to_equal(1)
```

</details>

#### preserves other entries

- var b = PersistentMapBuilder new
- b set
- b set
- b set
- b remove
   - Expected: b.get("a") equals `1`
   - Expected: b.get("c") equals `3`
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.set("c", 3)
b.remove("b")
expect(b.get("a")).to_equal(1)
expect(b.get("c")).to_equal(3)
expect(b.len()).to_equal(2)
```

</details>

#### remove non-existent key is safe

- var b = PersistentMapBuilder new
- b set
- b remove
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.remove("zzz")
expect(b.len()).to_equal(1)
```

</details>

### clear

#### removes all entries

- var b = PersistentMapBuilder new
- b set
- b set
- b clear
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.clear()
expect(b.len()).to_equal(0)
expect(b.is_empty()).to_equal(true)
```

</details>

#### allows set after clear

- var b = PersistentMapBuilder new
- b set
- b clear
- b set
   - Expected: b.len() equals `1`
   - Expected: b.get("b") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.clear()
b.set("b", 2)
expect(b.len()).to_equal(1)
expect(b.get("b")).to_equal(2)
expect(b.get("a")).to_be_nil()
```

</details>

### keys and values

#### returns correct keys

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: k.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 10)
b.set("y", 20)
val k = b.keys()
expect(k.len()).to_equal(2)
```

</details>

#### returns correct values

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: v.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 10)
b.set("y", 20)
val v = b.values()
expect(v.len()).to_equal(2)
```

</details>

#### empty builder has empty keys and values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
expect(b.keys().len()).to_equal(0)
expect(b.values().len()).to_equal(0)
```

</details>

### to_entries

#### returns key-value pairs

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: entries.len() equals `2`
   - Expected: first[0] equals `a`
   - Expected: first[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
val entries = b.to_entries()
expect(entries.len()).to_equal(2)
val first = entries[0]
expect(first[0]).to_equal("a")
expect(first[1]).to_equal(1)
```

</details>

#### empty builder returns empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PersistentMapBuilder.new()
val entries = b.to_entries()
expect(entries.len()).to_equal(0)
```

</details>

### build and freeze

#### returns entries as array of pairs

- var b = PersistentMapBuilder new
- b set
- b set
   - Expected: entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("name", "Alice")
b.set("age", 30)
val entries = b.build()
expect(entries.len()).to_equal(2)
```

</details>

#### marks builder as frozen

- var b = PersistentMapBuilder new
- b set
- b build
   - Expected: b.is_frozen() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 1)
b.build()
expect(b.is_frozen()).to_equal(true)
```

</details>

#### set is no-op after freeze

- var b = PersistentMapBuilder new
- b set
- b build
- b set
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.set("b", 2)
expect(b.len()).to_equal(1)
expect(b.get("b")).to_be_nil()
```

</details>

#### set_all is no-op after freeze

- var b = PersistentMapBuilder new
- b set
- b build
- b set all
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.set_all([["b", 2], ["c", 3]])
expect(b.len()).to_equal(1)
```

</details>

#### remove is no-op after freeze

- var b = PersistentMapBuilder new
- b set
- b set
- b build
- b remove
   - Expected: b.len() equals `2`
   - Expected: b.get("a") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.build()
b.remove("a")
expect(b.len()).to_equal(2)
expect(b.get("a")).to_equal(1)
```

</details>

#### clear is no-op after freeze

- var b = PersistentMapBuilder new
- b set
- b build
- b clear
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.clear()
expect(b.len()).to_equal(1)
```

</details>

#### reads still work after freeze

- var b = PersistentMapBuilder new
- b set
- b set
- b build
   - Expected: b.len() equals `2`
   - Expected: b.get("x") equals `42`
   - Expected: b contains `y`
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("x", 42)
b.set("y", 99)
b.build()
expect(b.len()).to_equal(2)
expect(b.get("x")).to_equal(42)
expect(b.contains("y")).to_equal(true)
expect(b.is_empty()).to_equal(false)
```

</details>

#### build returns well-formed entries

- var b = PersistentMapBuilder new
- b set
   - Expected: entries.len() equals `1`
   - Expected: pair[0] equals `key`
   - Expected: pair[1] equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("key", "value")
val entries = b.build()
expect(entries.len()).to_equal(1)
val pair = entries[0]
expect(pair[0]).to_equal("key")
expect(pair[1]).to_equal("value")
```

</details>

### edge cases

#### empty key string

- var b = PersistentMapBuilder new
- b set
   - Expected: b.get("") equals `empty_key`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("", "empty_key")
expect(b.get("")).to_equal("empty_key")
expect(b.len()).to_equal(1)
```

</details>

#### nil value stored and retrieved

- var b = PersistentMapBuilder new
- b set
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("nil_val", nil)
expect(b.len()).to_equal(1)
```

</details>

#### overwrite then remove

- var b = PersistentMapBuilder new
- b set
- b set
- b remove
   - Expected: b.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("a", 2)
b.remove("a")
expect(b.len()).to_equal(0)
expect(b.get("a")).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentVecBuilder
- creation
- from factory
- push
- push_all
- set_at
- pop
- clear
- get
- to_array
- build and freeze
- PersistentMapBuilder
- creation
- from_entries factory
- set and get
- set_all
- contains
- remove
- clear
- keys and values
- to_entries
- build and freeze
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
