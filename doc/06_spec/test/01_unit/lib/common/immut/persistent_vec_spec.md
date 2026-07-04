# Persistent Vec Specification

> <details>

<!-- sdn-diagram:id=persistent_vec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_vec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_vec_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_vec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 92 | 92 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Vec Specification

## Scenarios

### PersistentVec

### empty vector

#### has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.len()).to_equal(0)
```

</details>

#### is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.is_empty()).to_equal(true)
```

</details>

#### get returns nil for any index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.get(0)).to_be_nil()
expect(v.get(5)).to_be_nil()
```

</details>

#### first returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.first()).to_be_nil()
```

</details>

#### last returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.last()).to_be_nil()
```

</details>

#### to_array returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val arr = v.to_array()
expect(arr.len()).to_equal(0)
```

</details>

#### pop returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val v2 = v.pop()
expect(v2.len()).to_equal(0)
expect(v2.is_empty()).to_equal(true)
```

</details>

### push

#### adds single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(42)
expect(v.len()).to_equal(1)
expect(v.get(0)).to_equal(42)
```

</details>

#### adds multiple elements in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(10).push(20).push(30)
expect(v.len()).to_equal(3)
expect(v.get(0)).to_equal(10)
expect(v.get(1)).to_equal(20)
expect(v.get(2)).to_equal(30)
```

</details>

#### is no longer empty after push

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(1)
expect(v.is_empty()).to_equal(false)
```

</details>

#### supports mixed types

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(1).push("two").push(nil)
expect(v.len()).to_equal(3)
expect(v.get(0)).to_equal(1)
expect(v.get(1)).to_equal("two")
expect(v.get(2)).to_be_nil()
```

</details>

### get

#### retrieves element at valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40, 50])
expect(v.get(0)).to_equal(10)
expect(v.get(2)).to_equal(30)
expect(v.get(4)).to_equal(50)
```

</details>

#### returns nil for index beyond length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
expect(v.get(3)).to_be_nil()
expect(v.get(100)).to_be_nil()
```

</details>

#### supports negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40])
expect(v.get(-1)).to_equal(40)
expect(v.get(-2)).to_equal(30)
expect(v.get(-4)).to_equal(10)
```

</details>

#### returns nil for negative index beyond bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2])
expect(v.get(-3)).to_be_nil()
expect(v.get(-10)).to_be_nil()
```

</details>

### set

#### replaces element at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.set(1, 99)
expect(v2.get(1)).to_equal(99)
```

</details>

#### returns new vector - original unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = PersistentVec.from_array([10, 20, 30])
val v2 = v1.set(0, 99)
expect(v1.get(0)).to_equal(10)
expect(v2.get(0)).to_equal(99)
```

</details>

#### preserves other elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4, 5])
val v2 = v.set(2, 99)
expect(v2.get(0)).to_equal(1)
expect(v2.get(1)).to_equal(2)
expect(v2.get(2)).to_equal(99)
expect(v2.get(3)).to_equal(4)
expect(v2.get(4)).to_equal(5)
```

</details>

#### supports negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.set(-1, 99)
expect(v2.get(2)).to_equal(99)
```

</details>

#### returns self for out of bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.set(10, 99)
expect(v2.len()).to_equal(3)
expect(v2.get(0)).to_equal(1)
```

</details>

### pop

#### removes last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.pop()
expect(v2.len()).to_equal(2)
expect(v2.get(0)).to_equal(1)
expect(v2.get(1)).to_equal(2)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = PersistentVec.from_array([10, 20, 30])
val v2 = v1.pop()
expect(v1.len()).to_equal(3)
expect(v1.get(2)).to_equal(30)
expect(v2.len()).to_equal(2)
```

</details>

#### pop to single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2]).pop()
expect(v.len()).to_equal(1)
expect(v.get(0)).to_equal(1)
```

</details>

#### pop to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([42]).pop()
expect(v.len()).to_equal(0)
expect(v.is_empty()).to_equal(true)
```

</details>

### first and last

#### first returns element at index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([5, 10, 15])
expect(v.first()).to_equal(5)
```

</details>

#### last returns element at last index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([5, 10, 15])
expect(v.last()).to_equal(15)
```

</details>

#### first and last are same for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([42])
expect(v.first()).to_equal(42)
expect(v.last()).to_equal(42)
```

</details>

### from_array

#### builds from array preserving order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
expect(v.len()).to_equal(3)
expect(v.get(0)).to_equal(10)
expect(v.get(1)).to_equal(20)
expect(v.get(2)).to_equal(30)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([])
expect(v.len()).to_equal(0)
expect(v.is_empty()).to_equal(true)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([99])
expect(v.len()).to_equal(1)
expect(v.get(0)).to_equal(99)
```

</details>

### of

#### is alias for from_array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.of([5, 10, 15])
expect(v.len()).to_equal(3)
expect(v.get(0)).to_equal(5)
expect(v.get(2)).to_equal(15)
```

</details>

### repeat

#### creates vector with repeated value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.repeat(7, 5)
expect(v.len()).to_equal(5)
expect(v.get(0)).to_equal(7)
expect(v.get(4)).to_equal(7)
```

</details>

#### repeat zero gives empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.repeat(99, 0)
expect(v.len()).to_equal(0)
expect(v.is_empty()).to_equal(true)
```

</details>

### range

#### creates integer range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.range(0, 5)
expect(v.len()).to_equal(5)
expect(v.get(0)).to_equal(0)
expect(v.get(4)).to_equal(4)
```

</details>

#### creates non-zero start range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.range(3, 7)
expect(v.len()).to_equal(4)
expect(v.get(0)).to_equal(3)
expect(v.get(3)).to_equal(6)
```

</details>

#### empty range when start equals end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.range(5, 5)
expect(v.len()).to_equal(0)
expect(v.is_empty()).to_equal(true)
```

</details>

### persistence

#### original unchanged after push

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v0 = PersistentVec.empty()
val v1 = v0.push(1)
val v2 = v1.push(2)
val v3 = v2.push(3)
expect(v0.len()).to_equal(0)
expect(v1.len()).to_equal(1)
expect(v2.len()).to_equal(2)
expect(v3.len()).to_equal(3)
```

</details>

#### branches share structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentVec.from_array([1, 2, 3])
val branch_a = base.push(40)
val branch_b = base.push(50)
expect(base.len()).to_equal(3)
expect(branch_a.len()).to_equal(4)
expect(branch_b.len()).to_equal(4)
expect(branch_a.get(3)).to_equal(40)
expect(branch_b.get(3)).to_equal(50)
# Base elements identical in both branches
expect(branch_a.get(0)).to_equal(1)
expect(branch_b.get(0)).to_equal(1)
```

</details>

#### set does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = PersistentVec.from_array([10, 20, 30])
val v2 = v1.set(1, 99)
expect(v1.get(1)).to_equal(20)
expect(v2.get(1)).to_equal(99)
```

</details>

#### pop does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v1 = PersistentVec.from_array([1, 2, 3])
val v2 = v1.pop()
expect(v1.len()).to_equal(3)
expect(v1.get(2)).to_equal(3)
expect(v2.len()).to_equal(2)
```

</details>

### slice

#### takes a slice from the middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40, 50])
val s = v.slice(1, 4)
expect(s.len()).to_equal(3)
expect(s.get(0)).to_equal(20)
expect(s.get(1)).to_equal(30)
expect(s.get(2)).to_equal(40)
```

</details>

#### full range returns all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val s = v.slice(0, 3)
expect(s.len()).to_equal(3)
expect(s.get(0)).to_equal(1)
expect(s.get(2)).to_equal(3)
```

</details>

#### empty slice when start equals end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val s = v.slice(2, 2)
expect(s.len()).to_equal(0)
```

</details>

#### clamps end to size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val s = v.slice(1, 100)
expect(s.len()).to_equal(2)
expect(s.get(0)).to_equal(2)
```

</details>

### concat

#### concatenates two vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PersistentVec.from_array([1, 2])
val b = PersistentVec.from_array([3, 4])
val c = a.concat(b)
expect(c.len()).to_equal(4)
expect(c.get(0)).to_equal(1)
expect(c.get(1)).to_equal(2)
expect(c.get(2)).to_equal(3)
expect(c.get(3)).to_equal(4)
```

</details>

#### concat with empty returns same content

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val empty = PersistentVec.empty()
val c = v.concat(empty)
expect(c.len()).to_equal(3)
expect(c.get(0)).to_equal(1)
```

</details>

#### empty concat with other returns other

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = PersistentVec.empty()
val v = PersistentVec.from_array([10, 20])
val c = empty.concat(v)
expect(c.len()).to_equal(2)
expect(c.get(0)).to_equal(10)
```

</details>

#### does not modify originals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PersistentVec.from_array([1])
val b = PersistentVec.from_array([2])
val c = a.concat(b)
expect(a.len()).to_equal(1)
expect(b.len()).to_equal(1)
expect(c.len()).to_equal(2)
```

</details>

### map

#### applies function to each element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val doubled = v.map(_1 * 2)
expect(doubled.len()).to_equal(3)
expect(doubled.get(0)).to_equal(2)
expect(doubled.get(1)).to_equal(4)
expect(doubled.get(2)).to_equal(6)
```

</details>

#### preserves length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
val result = v.map(_1 + 1)
expect(result.len()).to_equal(3)
```

</details>

#### empty vector map is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val result = v.map(_1 * 2)
expect(result.len()).to_equal(0)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.map(_1 * 10)
expect(v.get(0)).to_equal(1)
expect(v2.get(0)).to_equal(10)
```

</details>

### filter

#### keeps matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4, 5, 6])
val evens = v.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(3)
expect(evens.get(0)).to_equal(2)
expect(evens.get(1)).to_equal(4)
expect(evens.get(2)).to_equal(6)
```

</details>

#### returns empty when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 3, 5])
val evens = v.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(0)
```

</details>

#### returns all when everything matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([2, 4, 6])
val evens = v.filter(_1 % 2 == 0)
expect(evens.len()).to_equal(3)
```

</details>

### fold

#### accumulates sum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4])
val sum = v.fold(0, \acc, x: acc + x)
expect(sum).to_equal(10)
```

</details>

#### accumulates product

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4])
val product = v.fold(1, \acc, x: acc * x)
expect(product).to_equal(24)
```

</details>

#### returns init for empty vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val result = v.fold(42, \acc, x: acc + x)
expect(result).to_equal(42)
```

</details>

#### single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([5])
val result = v.fold(0, \acc, x: acc + x)
expect(result).to_equal(5)
```

</details>

### take

#### takes first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40, 50])
val t = v.take(3)
expect(t.len()).to_equal(3)
expect(t.get(0)).to_equal(10)
expect(t.get(2)).to_equal(30)
```

</details>

#### takes zero returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val t = v.take(0)
expect(t.len()).to_equal(0)
```

</details>

#### takes more than length returns all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2])
val t = v.take(10)
expect(t.len()).to_equal(2)
```

</details>

### drop

#### drops first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40, 50])
val d = v.drop(2)
expect(d.len()).to_equal(3)
expect(d.get(0)).to_equal(30)
expect(d.get(2)).to_equal(50)
```

</details>

#### drops zero returns all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val d = v.drop(0)
expect(d.len()).to_equal(3)
```

</details>

#### drops more than length returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2])
val d = v.drop(10)
expect(d.len()).to_equal(0)
```

</details>

### contains

#### finds existing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
expect(v.contains(20)).to_equal(true)
```

</details>

#### returns false for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
expect(v.contains(99)).to_equal(false)
```

</details>

#### returns false for empty vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.contains(1)).to_equal(false)
```

</details>

#### finds string elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array(["a", "b", "c"])
expect(v.contains("b")).to_equal(true)
expect(v.contains("z")).to_equal(false)
```

</details>

### index_of

#### finds index of existing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30, 40])
expect(v.index_of(30)).to_equal(2)
```

</details>

#### returns -1 for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
expect(v.index_of(99)).to_equal(-1)
```

</details>

#### returns first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([5, 10, 5, 10])
expect(v.index_of(10)).to_equal(1)
```

</details>

#### returns -1 for empty vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
expect(v.index_of(1)).to_equal(-1)
```

</details>

### reverse

#### reverses the vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val r = v.reverse()
expect(r.get(0)).to_equal(3)
expect(r.get(1)).to_equal(2)
expect(r.get(2)).to_equal(1)
```

</details>

#### preserves length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4])
val r = v.reverse()
expect(r.len()).to_equal(4)
```

</details>

#### reverse of single element is same

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([42])
val r = v.reverse()
expect(r.get(0)).to_equal(42)
expect(r.len()).to_equal(1)
```

</details>

#### reverse of empty is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val r = v.reverse()
expect(r.len()).to_equal(0)
```

</details>

#### does not modify original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val r = v.reverse()
expect(v.get(0)).to_equal(1)
expect(r.get(0)).to_equal(3)
```

</details>

### to_array

#### converts to array in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([10, 20, 30])
val arr = v.to_array()
expect(arr.len()).to_equal(3)
expect(arr[0]).to_equal(10)
expect(arr[1]).to_equal(20)
expect(arr[2]).to_equal(30)
```

</details>

#### empty vector gives empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty()
val arr = v.to_array()
expect(arr.len()).to_equal(0)
```

</details>

#### round-trips through array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [5, 10, 15, 20]
val v = PersistentVec.from_array(original)
val arr = v.to_array()
expect(arr.len()).to_equal(4)
expect(arr[0]).to_equal(5)
expect(arr[3]).to_equal(20)
```

</details>

### each

#### visits all elements

- v each
   - Expected: v.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
# Note: each uses closures; nested closures cannot modify
# captured vars in interpreter mode. We just test it runs.
v.each(\x: x)
expect(v.len()).to_equal(3)
```

</details>

### stress test

#### push and get many elements via helper fn

- fn run push stress
- var v = PersistentVec empty
- v = v push
- v len
   - Expected: run_push_stress() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_push_stress() -> i64:
    var v = PersistentVec.empty()
    var i = 0
    while i < 200:
        v = v.push(i)
        i = i + 1
    v.len()
expect(run_push_stress()).to_equal(200)
```

</details>

#### verify elements after many pushes

- fn run verify stress
- var v = PersistentVec empty
- v = v push
   - Expected: run_verify_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_verify_stress() -> i64:
    var v = PersistentVec.empty()
    var i = 0
    while i < 100:
        v = v.push(i * 10)
        i = i + 1
    var ok_count = 0
    i = 0
    while i < 100:
        if v.get(i) == i * 10:
            ok_count = ok_count + 1
        i = i + 1
    ok_count
expect(run_verify_stress()).to_equal(100)
```

</details>

#### push then pop many elements

- fn run pop stress
- var v = PersistentVec empty
- v = v push
- v = v pop
- v len
   - Expected: run_pop_stress() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_pop_stress() -> i64:
    var v = PersistentVec.empty()
    var i = 0
    while i < 50:
        v = v.push(i)
        i = i + 1
    i = 0
    while i < 25:
        v = v.pop()
        i = i + 1
    v.len()
expect(run_pop_stress()).to_equal(25)
```

</details>

#### range creates correct elements

- fn run range stress
   - Expected: run_range_stress() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_range_stress() -> i64:
    val v = PersistentVec.range(0, 100)
    var ok_count = 0
    var i = 0
    while i < 100:
        if v.get(i) == i:
            ok_count = ok_count + 1
        i = i + 1
    ok_count
expect(run_range_stress()).to_equal(100)
```

</details>

### edge cases

#### set same value returns equivalent vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.set(1, 2)
expect(v2.get(1)).to_equal(2)
expect(v2.len()).to_equal(3)
```

</details>

#### nil value stored and retrieved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.empty().push(nil)
expect(v.len()).to_equal(1)
expect(v.get(0)).to_be_nil()
```

</details>

#### push after pop restores length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3])
val v2 = v.pop().push(99)
expect(v2.len()).to_equal(3)
expect(v2.get(2)).to_equal(99)
```

</details>

#### concat two empties is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = PersistentVec.empty()
val b = PersistentVec.empty()
val c = a.concat(b)
expect(c.len()).to_equal(0)
expect(c.is_empty()).to_equal(true)
```

</details>

#### filter then map

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4, 5, 6])
val result = v.filter(_1 % 2 == 0).map(_1 * 10)
expect(result.len()).to_equal(3)
expect(result.get(0)).to_equal(20)
expect(result.get(1)).to_equal(40)
expect(result.get(2)).to_equal(60)
```

</details>

#### take and drop partition the vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = PersistentVec.from_array([1, 2, 3, 4, 5])
val head = v.take(3)
val tail = v.drop(3)
expect(head.len()).to_equal(3)
expect(tail.len()).to_equal(2)
expect(head.get(0)).to_equal(1)
expect(tail.get(0)).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/persistent_vec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentVec
- empty vector
- push
- get
- set
- pop
- first and last
- from_array
- of
- repeat
- range
- persistence
- slice
- concat
- map
- filter
- fold
- take
- drop
- contains
- index_of
- reverse
- to_array
- each
- stress test
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 92 |
| Active scenarios | 92 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
