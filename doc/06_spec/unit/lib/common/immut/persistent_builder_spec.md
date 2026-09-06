# persistent_builder_spec

> Purpose: Prove that PersistentVecBuilder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# persistent_builder_spec

Purpose: Prove that PersistentVecBuilder.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/immut/persistent_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that PersistentVecBuilder.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### PersistentVecBuilder

### creation

#### starts empty

- starts empty
- Verify: starts empty
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty")
step("Verify: starts empty")
# @req: REQ-LIB-COMMON-001
val b = PersistentVecBuilder.new()
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

#### starts not frozen

- starts not frozen
- Verify: starts not frozen
   - Expected: b.is_frozen() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts not frozen")
step("Verify: starts not frozen")
val b = PersistentVecBuilder.new()
expect(b.is_frozen()).to_equal(false)
```

</details>

### from factory

#### pre-populates with items

- pre-populates with items
- Verify: pre-populates with items
   - Expected: b.len() equals `3`
   - Expected: b.get(0) equals `10`
   - Expected: b.get(2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pre-populates with items")
step("Verify: pre-populates with items")
val b = PersistentVecBuilder.from([10, 20, 30])
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(b.get(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(b.get(2)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### is not frozen after creation

- is not frozen after creation
- Verify: is not frozen after creation
   - Expected: b.is_frozen() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not frozen after creation")
step("Verify: is not frozen after creation")
val b = PersistentVecBuilder.from([1, 2])
expect(b.is_frozen()).to_equal(false)
```

</details>

#### empty array gives empty builder

- empty array gives empty builder
- Verify: empty array gives empty builder
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty array gives empty builder")
step("Verify: empty array gives empty builder")
val b = PersistentVecBuilder.from([])
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

### push

#### adds single element

- adds single element
- Verify: adds single element
   - Expected: b.len() equals `1`
   - Expected: b.get(0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds single element")
step("Verify: adds single element")
var b = PersistentVecBuilder.new()
b.push(42)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(0)).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### adds multiple elements in order

- adds multiple elements in order
- Verify: adds multiple elements in order
   - Expected: b.len() equals `3`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds multiple elements in order")
step("Verify: adds multiple elements in order")
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.push(3)
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(b.get(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get(2)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### is no longer empty after push

- is no longer empty after push
- Verify: is no longer empty after push
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is no longer empty after push")
step("Verify: is no longer empty after push")
var b = PersistentVecBuilder.new()
b.push(99)
expect(b.is_empty()).to_equal(false)
```

</details>

### push_all

#### adds all items from array

- adds all items from array
- Verify: adds all items from array
   - Expected: b.len() equals `3`
   - Expected: b.get(0) equals `10`
   - Expected: b.get(2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds all items from array")
step("Verify: adds all items from array")
var b = PersistentVecBuilder.new()
b.push_all([10, 20, 30])
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(b.get(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(b.get(2)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### appends to existing items

- appends to existing items
- Verify: appends to existing items
   - Expected: b.len() equals `4`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(3) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to existing items")
step("Verify: appends to existing items")
var b = PersistentVecBuilder.new()
b.push(1)
b.push_all([2, 3, 4])
expect(b.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(b.get(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(3)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### empty array is no-op

- empty array is no-op
- Verify: empty array is no-op
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty array is no-op")
step("Verify: empty array is no-op")
var b = PersistentVecBuilder.new()
b.push(1)
b.push_all([])
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### set_at

#### replaces element at index

- replaces element at index
- Verify: replaces element at index
   - Expected: b.get(1) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces element at index")
step("Verify: replaces element at index")
var b = PersistentVecBuilder.from([10, 20, 30])
b.set_at(1, 99)
expect(b.get(1)).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

#### preserves other elements

- preserves other elements
- Verify: preserves other elements
   - Expected: b.get(0) equals `99`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves other elements")
step("Verify: preserves other elements")
var b = PersistentVecBuilder.from([1, 2, 3])
b.set_at(0, 99)
expect(b.get(0)).to_equal(99)  # oracle: 99 — named expected value from the requirement
expect(b.get(1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get(2)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### ignores negative index

- ignores negative index
- Verify: ignores negative index
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`
   - Expected: b.get(2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores negative index")
step("Verify: ignores negative index")
var b = PersistentVecBuilder.from([1, 2, 3])
b.set_at(-1, 99)
expect(b.get(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get(2)).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### ignores out of bounds index

- ignores out of bounds index
- Verify: ignores out of bounds index
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores out of bounds index")
step("Verify: ignores out of bounds index")
var b = PersistentVecBuilder.from([1, 2])
b.set_at(10, 99)
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### pop

#### removes last element

- removes last element
- Verify: removes last element
   - Expected: b.len() equals `2`
   - Expected: b.get(0) equals `1`
   - Expected: b.get(1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes last element")
step("Verify: removes last element")
var b = PersistentVecBuilder.from([1, 2, 3])
b.pop()
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get(0)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(1)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### clear

#### removes all elements

- removes all elements
- Verify: removes all elements
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes all elements")
step("Verify: removes all elements")
var b = PersistentVecBuilder.from([1, 2, 3])
b.clear()
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

#### allows push after clear

- allows push after clear
- Verify: allows push after clear
   - Expected: b.len() equals `1`
   - Expected: b.get(0) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows push after clear")
step("Verify: allows push after clear")
var b = PersistentVecBuilder.from([1, 2])
b.clear()
b.push(99)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get(0)).to_equal(99)  # oracle: 99 — named expected value from the requirement
```

</details>

### get

#### returns element at index

- returns element at index
- Verify: returns element at index
   - Expected: b.get(0) equals `10`
   - Expected: b.get(1) equals `20`
   - Expected: b.get(2) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns element at index")
step("Verify: returns element at index")
val b = PersistentVecBuilder.from([10, 20, 30])
expect(b.get(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(b.get(1)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(b.get(2)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### returns nil for out of bounds

- returns nil for out of bounds
- Verify: returns nil for out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for out of bounds")
step("Verify: returns nil for out of bounds")
val b = PersistentVecBuilder.from([1, 2])
expect(b.get(5)).to_be_nil()
```

</details>

#### returns nil for negative index

- returns nil for negative index
- Verify: returns nil for negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for negative index")
step("Verify: returns nil for negative index")
val b = PersistentVecBuilder.from([1, 2])
expect(b.get(-1)).to_be_nil()
```

</details>

### to_array

#### returns copy of items

- returns copy of items
- Verify: returns copy of items
   - Expected: arr.len() equals `3`
   - Expected: arr[0] equals `1`
   - Expected: arr[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns copy of items")
step("Verify: returns copy of items")
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.push(3)
val arr = b.to_array()
expect(arr.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(arr[0]).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(arr[2]).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### empty builder returns empty array

- empty builder returns empty array
- Verify: empty builder returns empty array
   - Expected: arr.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty builder returns empty array")
step("Verify: empty builder returns empty array")
val b = PersistentVecBuilder.new()
val arr = b.to_array()
expect(arr.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### build and freeze

#### returns items as array

- returns items as array
- Verify: returns items as array
   - Expected: items.len() equals `3`
   - Expected: items[0] equals `10`
   - Expected: items[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns items as array")
step("Verify: returns items as array")
var b = PersistentVecBuilder.new()
b.push(10)
b.push(20)
b.push(30)
val items = b.build()
expect(items.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(items[0]).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(items[2]).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### marks builder as frozen

- marks builder as frozen
- Verify: marks builder as frozen
   - Expected: b.is_frozen() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks builder as frozen")
step("Verify: marks builder as frozen")
var b = PersistentVecBuilder.new()
b.push(1)
b.build()
expect(b.is_frozen()).to_equal(true)
```

</details>

#### push is no-op after freeze

- push is no-op after freeze
- Verify: push is no-op after freeze
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push is no-op after freeze")
step("Verify: push is no-op after freeze")
var b = PersistentVecBuilder.new()
b.push(1)
b.push(2)
b.build()
b.push(3)
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### push_all is no-op after freeze

- push_all is no-op after freeze
- Verify: push_all is no-op after freeze
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_all is no-op after freeze")
step("Verify: push_all is no-op after freeze")
var b = PersistentVecBuilder.new()
b.push(1)
b.build()
b.push_all([2, 3, 4])
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### set_at is no-op after freeze

- set_at is no-op after freeze
- Verify: set_at is no-op after freeze
   - Expected: b.get(0) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_at is no-op after freeze")
step("Verify: set_at is no-op after freeze")
var b = PersistentVecBuilder.from([10, 20])
b.build()
b.set_at(0, 99)
expect(b.get(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### clear is no-op after freeze

- clear is no-op after freeze
- Verify: clear is no-op after freeze
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear is no-op after freeze")
step("Verify: clear is no-op after freeze")
var b = PersistentVecBuilder.from([1, 2, 3])
b.build()
b.clear()
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### reads still work after freeze

- reads still work after freeze
- Verify: reads still work after freeze
   - Expected: b.len() equals `2`
   - Expected: b.get(0) equals `10`
   - Expected: b.get(1) equals `20`
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads still work after freeze")
step("Verify: reads still work after freeze")
var b = PersistentVecBuilder.new()
b.push(10)
b.push(20)
b.build()
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(b.get(1)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(b.is_empty()).to_equal(false)
```

</details>

### PersistentMapBuilder

### creation

#### starts empty

- starts empty
- Verify: starts empty
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty")
step("Verify: starts empty")
val b = PersistentMapBuilder.new()
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

#### starts not frozen

- starts not frozen
- Verify: starts not frozen
   - Expected: b.is_frozen() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts not frozen")
step("Verify: starts not frozen")
val b = PersistentMapBuilder.new()
expect(b.is_frozen()).to_equal(false)
```

</details>

### from_entries factory

#### pre-populates with entries

- pre-populates with entries
- Verify: pre-populates with entries
   - Expected: b.len() equals `2`
   - Expected: b.get("a") equals `1`
   - Expected: b.get("b") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pre-populates with entries")
step("Verify: pre-populates with entries")
val b = PersistentMapBuilder.from_entries([["a", 1], ["b", 2]])
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get("a")).to_equal(1)
expect(b.get("b")).to_equal(2)
```

</details>

#### is not frozen after creation

- is not frozen after creation
- Verify: is not frozen after creation
   - Expected: b.is_frozen() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not frozen after creation")
step("Verify: is not frozen after creation")
val b = PersistentMapBuilder.from_entries([["x", 10]])
expect(b.is_frozen()).to_equal(false)
```

</details>

#### empty entries gives empty builder

- empty entries gives empty builder
- Verify: empty entries gives empty builder
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty entries gives empty builder")
step("Verify: empty entries gives empty builder")
val b = PersistentMapBuilder.from_entries([])
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

#### handles duplicate keys in entries

- handles duplicate keys in entries
- Verify: handles duplicate keys in entries
   - Expected: b.len() equals `1`
   - Expected: b.get("a") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles duplicate keys in entries")
step("Verify: handles duplicate keys in entries")
val b = PersistentMapBuilder.from_entries([["a", 1], ["a", 2]])
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get("a")).to_equal(2)
```

</details>

### set and get

#### stores and retrieves a value

- stores and retrieves a value
- Verify: stores and retrieves a value
   - Expected: b.get("name") equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores and retrieves a value")
step("Verify: stores and retrieves a value")
var b = PersistentMapBuilder.new()
b.set("name", "Alice")
expect(b.get("name")).to_equal("Alice")
```

</details>

#### stores multiple key-value pairs

- stores multiple key-value pairs
- Verify: stores multiple key-value pairs
   - Expected: b.len() equals `3`
   - Expected: b.get("a") equals `1`
   - Expected: b.get("b") equals `2`
   - Expected: b.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores multiple key-value pairs")
step("Verify: stores multiple key-value pairs")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.set("c", 3)
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(b.get("a")).to_equal(1)
expect(b.get("b")).to_equal(2)
expect(b.get("c")).to_equal(3)
```

</details>

#### overwrites existing key

- overwrites existing key
- Verify: overwrites existing key
   - Expected: b.get("key") equals `new`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrites existing key")
step("Verify: overwrites existing key")
var b = PersistentMapBuilder.new()
b.set("key", "old")
b.set("key", "new")
expect(b.get("key")).to_equal("new")
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
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
val b = PersistentMapBuilder.new()
expect(b.get("nothing")).to_be_nil()
```

</details>

#### stores integer keys

- stores integer keys
- Verify: stores integer keys
   - Expected: b.get(1) equals `one`
   - Expected: b.get(2) equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores integer keys")
step("Verify: stores integer keys")
var b = PersistentMapBuilder.new()
b.set(1, "one")
b.set(2, "two")
expect(b.get(1)).to_equal("one")
expect(b.get(2)).to_equal("two")
```

</details>

### set_all

#### adds multiple entries

- adds multiple entries
- Verify: adds multiple entries
   - Expected: b.len() equals `3`
   - Expected: b.get("x") equals `10`
   - Expected: b.get("z") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds multiple entries")
step("Verify: adds multiple entries")
var b = PersistentMapBuilder.new()
b.set_all([["x", 10], ["y", 20], ["z", 30]])
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(b.get("x")).to_equal(10)
expect(b.get("z")).to_equal(30)
```

</details>

#### appends to existing entries

- appends to existing entries
- Verify: appends to existing entries
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends to existing entries")
step("Verify: appends to existing entries")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set_all([["b", 2], ["c", 3]])
expect(b.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

### contains

#### returns true for existing key

- returns true for existing key
- Verify: returns true for existing key
   - Expected: b contains `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for existing key")
step("Verify: returns true for existing key")
var b = PersistentMapBuilder.new()
b.set("x", 42)
expect(b.contains("x")).to_equal(true)
```

</details>

#### returns false for missing key

- returns false for missing key
- Verify: returns false for missing key
   - Expected: b does not contain `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for missing key")
step("Verify: returns false for missing key")
var b = PersistentMapBuilder.new()
b.set("x", 42)
expect(b.contains("y")).to_equal(false)
```

</details>

#### returns false for empty builder

- returns false for empty builder
- Verify: returns false for empty builder
   - Expected: b does not contain `anything`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty builder")
step("Verify: returns false for empty builder")
val b = PersistentMapBuilder.new()
expect(b.contains("anything")).to_equal(false)
```

</details>

### remove

#### removes an existing key

- removes an existing key
- Verify: removes an existing key
   - Expected: b does not contain `a`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes an existing key")
step("Verify: removes an existing key")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.remove("a")
expect(b.get("a")).to_be_nil()
expect(b.contains("a")).to_equal(false)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### preserves other entries

- preserves other entries
- Verify: preserves other entries
   - Expected: b.get("a") equals `1`
   - Expected: b.get("c") equals `3`
   - Expected: b.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves other entries")
step("Verify: preserves other entries")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.set("c", 3)
b.remove("b")
expect(b.get("a")).to_equal(1)
expect(b.get("c")).to_equal(3)
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### remove non-existent key is safe

- remove non-existent key is safe
- Verify: remove non-existent key is safe
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove non-existent key is safe")
step("Verify: remove non-existent key is safe")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.remove("zzz")
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### clear

#### removes all entries

- removes all entries
- Verify: removes all entries
   - Expected: b.len() equals `0`
   - Expected: b.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes all entries")
step("Verify: removes all entries")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.clear()
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.is_empty()).to_equal(true)
```

</details>

#### allows set after clear

- allows set after clear
- Verify: allows set after clear
   - Expected: b.len() equals `1`
   - Expected: b.get("b") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows set after clear")
step("Verify: allows set after clear")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.clear()
b.set("b", 2)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get("b")).to_equal(2)
expect(b.get("a")).to_be_nil()
```

</details>

### keys and values

#### returns correct keys

- returns correct keys
- Verify: returns correct keys
   - Expected: k.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct keys")
step("Verify: returns correct keys")
var b = PersistentMapBuilder.new()
b.set("x", 10)
b.set("y", 20)
val k = b.keys()
expect(k.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### returns correct values

- returns correct values
- Verify: returns correct values
   - Expected: v.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct values")
step("Verify: returns correct values")
var b = PersistentMapBuilder.new()
b.set("x", 10)
b.set("y", 20)
val v = b.values()
expect(v.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### empty builder has empty keys and values

- empty builder has empty keys and values
- Verify: empty builder has empty keys and values
   - Expected: b.keys().len() equals `0`
   - Expected: b.values().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty builder has empty keys and values")
step("Verify: empty builder has empty keys and values")
val b = PersistentMapBuilder.new()
expect(b.keys().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.values().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### to_entries

#### returns key-value pairs

- returns key-value pairs
- Verify: returns key-value pairs
   - Expected: entries.len() equals `2`
   - Expected: first[0] equals `a`
   - Expected: first[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns key-value pairs")
step("Verify: returns key-value pairs")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
val entries = b.to_entries()
expect(entries.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
val first = entries[0]
expect(first[0]).to_equal("a")
expect(first[1]).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### empty builder returns empty entries

- empty builder returns empty entries
- Verify: empty builder returns empty entries
   - Expected: entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty builder returns empty entries")
step("Verify: empty builder returns empty entries")
val b = PersistentMapBuilder.new()
val entries = b.to_entries()
expect(entries.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### build and freeze

#### returns entries as array of pairs

- returns entries as array of pairs
- Verify: returns entries as array of pairs
   - Expected: entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns entries as array of pairs")
step("Verify: returns entries as array of pairs")
var b = PersistentMapBuilder.new()
b.set("name", "Alice")
b.set("age", 30)
val entries = b.build()
expect(entries.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### marks builder as frozen

- marks builder as frozen
- Verify: marks builder as frozen
   - Expected: b.is_frozen() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks builder as frozen")
step("Verify: marks builder as frozen")
var b = PersistentMapBuilder.new()
b.set("x", 1)
b.build()
expect(b.is_frozen()).to_equal(true)
```

</details>

#### set is no-op after freeze

- set is no-op after freeze
- Verify: set is no-op after freeze
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set is no-op after freeze")
step("Verify: set is no-op after freeze")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.set("b", 2)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(b.get("b")).to_be_nil()
```

</details>

#### set_all is no-op after freeze

- set_all is no-op after freeze
- Verify: set_all is no-op after freeze
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_all is no-op after freeze")
step("Verify: set_all is no-op after freeze")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.set_all([["b", 2], ["c", 3]])
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### remove is no-op after freeze

- remove is no-op after freeze
- Verify: remove is no-op after freeze
   - Expected: b.len() equals `2`
   - Expected: b.get("a") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove is no-op after freeze")
step("Verify: remove is no-op after freeze")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("b", 2)
b.build()
b.remove("a")
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get("a")).to_equal(1)
```

</details>

#### clear is no-op after freeze

- clear is no-op after freeze
- Verify: clear is no-op after freeze
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear is no-op after freeze")
step("Verify: clear is no-op after freeze")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.build()
b.clear()
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### reads still work after freeze

- reads still work after freeze
- Verify: reads still work after freeze
   - Expected: b.len() equals `2`
   - Expected: b.get("x") equals `42`
   - Expected: b contains `y`
   - Expected: b.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads still work after freeze")
step("Verify: reads still work after freeze")
var b = PersistentMapBuilder.new()
b.set("x", 42)
b.set("y", 99)
b.build()
expect(b.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(b.get("x")).to_equal(42)
expect(b.contains("y")).to_equal(true)
expect(b.is_empty()).to_equal(false)
```

</details>

#### build returns well-formed entries

- build returns well-formed entries
- Verify: build returns well-formed entries
   - Expected: entries.len() equals `1`
   - Expected: pair[0] equals `key`
   - Expected: pair[1] equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build returns well-formed entries")
step("Verify: build returns well-formed entries")
var b = PersistentMapBuilder.new()
b.set("key", "value")
val entries = b.build()
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val pair = entries[0]
expect(pair[0]).to_equal("key")
expect(pair[1]).to_equal("value")
```

</details>

### edge cases

#### empty key string

- empty key string
- Verify: empty key string
   - Expected: b.get("") equals `empty_key`
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty key string")
step("Verify: empty key string")
var b = PersistentMapBuilder.new()
b.set("", "empty_key")
expect(b.get("")).to_equal("empty_key")
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### nil value stored and retrieved

- nil value stored and retrieved
- Verify: nil value stored and retrieved
   - Expected: b.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil value stored and retrieved")
step("Verify: nil value stored and retrieved")
var b = PersistentMapBuilder.new()
b.set("nil_val", nil)
expect(b.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### overwrite then remove

- overwrite then remove
- Verify: overwrite then remove
   - Expected: b.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrite then remove")
step("Verify: overwrite then remove")
var b = PersistentMapBuilder.new()
b.set("a", 1)
b.set("a", 2)
b.remove("a")
expect(b.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(b.get("a")).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
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

- Canonical SPipe generation for source `b19f71db1faed8376f2d96d3e78a67d9515923299ab3672daf61731f53e11a90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b19f71db1faed8376f2d96d3e78a67d9515923299ab3672daf61731f53e11a90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b19f71db1faed8376f2d96d3e78a67d9515923299ab3672daf61731f53e11a90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/immut/persistent_builder_spec.spl
mirror: doc/06_spec/unit/lib/common/immut/persistent_builder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/immut/persistent_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/immut/persistent_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/immut/persistent_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/immut/persistent_builder_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_builder_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts not frozen' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/immut/persistent_builder_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pre-populates with items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
