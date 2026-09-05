# Persistent Vec Intensive Specification

> 1. expect true

<!-- sdn-diagram:id=persistent_vec_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=persistent_vec_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

persistent_vec_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=persistent_vec_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Vec Intensive Specification

## Scenarios

### PersistentVec intensive tests

### Basic operations

#### creates empty vec

1. expect true
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.new()
expect_true(vec.is_empty())
expect_len(vec, 0)
```

</details>

#### push adds element

1. expect true
2. expect len
   - Expected: vec2.get(0) equals `Some(42)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.new()
val vec2 = vec1.push(42)

expect_true(vec1.is_empty())
expect_len(vec2, 1)
expect(vec2.get(0)).to_equal(Some(42))
```

</details>

#### multiple pushes

1. var vec = MiniVec new
2. vec = vec push
3. expect len
   - Expected: vec.get(i) equals `Some(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..100:
    vec = vec.push(i)

expect_len(vec, 100)
for i in 0..100:
    expect(vec.get(i)).to_equal(Some(i))
```

</details>

### Indexing

#### get with positive index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([10, 20, 30])
expect(vec.get(0)).to_equal(Some(10))
expect(vec.get(1)).to_equal(Some(20))
expect(vec.get(2)).to_equal(Some(30))
```

</details>

#### get with negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([10, 20, 30])
expect(vec.get(-1)).to_equal(Some(30))
expect(vec.get(-2)).to_equal(Some(20))
expect(vec.get(-3)).to_equal(Some(10))
```

</details>

#### get out of bounds returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3])
expect(vec.get(3)).to_equal(nil)
expect(vec.get(-4)).to_equal(nil)
```

</details>

#### first and last

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3])
expect(vec.first()).to_equal(Some(1))
expect(vec.last()).to_equal(Some(3))
```

</details>

#### first/last on empty returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.new()
expect(vec.first()).to_equal(nil)
expect(vec.last()).to_equal(nil)
```

</details>

### Immutability

#### push doesn't modify original

1. expect len
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.push(4)

expect_len(vec1, 3)
expect_len(vec2, 4)
```

</details>

#### set creates new version

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.set(1, 99)

expect(vec1.get(1)).to_equal(Some(2))
expect(vec2.get(1)).to_equal(Some(99))
```

</details>

#### pop creates new version

1. expect len
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.pop()

expect_len(vec1, 3)
expect_len(vec2, 2)
```

</details>

### Set operation

#### set updates element

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.set(1, 99)

expect(vec2.get(0)).to_equal(Some(1))
expect(vec2.get(1)).to_equal(Some(99))
expect(vec2.get(2)).to_equal(Some(3))
```

</details>

#### set with negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.set(-1, 99)

expect(vec2.get(2)).to_equal(Some(99))
```

</details>

#### set out of bounds returns unchanged

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.set(10, 99)

expect_len(vec1, vec2.len())
```

</details>

### Pop operation

#### pop removes last element

1. expect len
   - Expected: vec2.get(0) equals `Some(1)`
   - Expected: vec2.get(1) equals `Some(2)`
   - Expected: vec2.get(2) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.pop()

expect_len(vec2, 2)
expect(vec2.get(0)).to_equal(Some(1))
expect(vec2.get(1)).to_equal(Some(2))
expect(vec2.get(2)).to_equal(nil)
```

</details>

#### pop from empty returns empty

1. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.new()
val vec2 = vec1.pop()

expect_true(vec2.is_empty())
```

</details>

#### pop single element

1. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.new().push(42)
val vec2 = vec1.pop()

expect_true(vec2.is_empty())
```

</details>

#### repeated pops

1. var vec = MiniVec from array
2. expect len
3. vec = vec pop
4. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.from_array([1, 2, 3, 4, 5])

var remaining = 5
for _ in 0..5:
    expect_len(vec, remaining)
    vec = vec.pop()
    remaining = remaining - 1

expect_true(vec.is_empty())
```

</details>

#### pop maintains correct values

1. var vec = MiniVec new
2. vec = vec push
3. vec = vec pop
4. expect len
   - Expected: vec.get(i) equals `Some(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..100:
    vec = vec.push(i)

for _ in 0..50:
    vec = vec.pop()

expect_len(vec, 50)
for i in 0..50:
    expect(vec.get(i)).to_equal(Some(i))
```

</details>

### Large vector (stress test tail buffer)

#### handles > 32 elements (forces tree usage)

1. var vec = MiniVec new
2. vec = vec push
3. expect len
   - Expected: vec.get(i) equals `Some(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..100:
    vec = vec.push(i)

expect_len(vec, 100)
for i in 0..100:
    expect(vec.get(i)).to_equal(Some(i))
```

</details>

#### tail buffer transition

1. var vec = MiniVec new
2. vec = vec push
3. vec = vec push
4. expect len
   - Expected: vec.get(i) equals `Some(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..32:
    vec = vec.push(i)

vec = vec.push(32)

expect_len(vec, 33)
for i in 0..33:
    expect(vec.get(i)).to_equal(Some(i))
```

</details>

### Bulk operations

#### concat combines vectors

1. expect len
   - Expected: vec3.to_array() equals `[1, 2, 3, 4, 5, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = MiniVec.from_array([4, 5, 6])
val vec3 = vec1.concat(vec2)

expect_len(vec3, 6)
expect(vec3.to_array()).to_equal([1, 2, 3, 4, 5, 6])
```

</details>

#### map transforms elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3])
val vec2 = vec1.map(_1 * 2)

expect(vec2.to_array()).to_equal([2, 4, 6])
```

</details>

#### filter keeps matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec1 = MiniVec.from_array([1, 2, 3, 4, 5, 6])
val vec2 = vec1.filter(_1 % 2 == 0)

expect(vec2.to_array()).to_equal([2, 4, 6])
```

</details>

#### fold reduces to single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3, 4, 5])
val sum = vec.fold(0, \acc, x: acc + x)

expect(sum).to_equal(15)
```

</details>

### Slicing operations

#### take first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3, 4, 5])
val taken = vec.take(3)

expect(taken.to_array()).to_equal([1, 2, 3])
```

</details>

#### drop first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3, 4, 5])
val dropped = vec.drop(2)

expect(dropped.to_array()).to_equal([3, 4, 5])
```

</details>

#### slice range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3, 4, 5])
val sliced = vec.slice(1, 4)

expect(sliced.to_array()).to_equal([2, 3, 4])
```

</details>

#### reverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3, 4, 5])
val reversed = vec.reverse()

expect(reversed.to_array()).to_equal([5, 4, 3, 2, 1])
```

</details>

### Work accounting

#### push 10000 elements efficiently

1. var vec = MiniVec new
2. vec = vec push
3. expect len
   - Expected: vec.work equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..10000:
    vec = vec.push(i)

expect_len(vec, 10000)
expect(vec.work).to_equal(10000)
```

</details>

#### random access does not change persistent history

1. var vec = MiniVec new
2. vec = vec push
3. expect len
   - Expected: vec.work equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..10000:
    vec = vec.push(i)

var index = 0
for _ in 0..1000:
    val _ = vec.get(index)
    index = index + 10

expect_len(vec, 10000)
expect(vec.work).to_equal(10000)
```

</details>

#### pop 1000 elements efficiently

1. var vec = MiniVec new
2. vec = vec push
3. vec = vec pop
4. expect true
   - Expected: vec.work equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()
for i in 0..1000:
    vec = vec.push(i)

for _ in 0..1000:
    vec = vec.pop()

expect_true(vec.is_empty())
expect(vec.work).to_equal(2000)
```

</details>

#### structural sharing is efficient

1. var base = MiniVec new
2. base = base push
3. versions = versions push
   - Expected: versions.len() equals `1000`
   - Expected: base.work equals `1000`
   - Expected: versions[0].work equals `1001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base = MiniVec.new()
for i in 0..1000:
    base = base.push(i)

var versions: [MiniVec] = []
for i in 0..1000:
    versions = versions.push(base.set(i, i * 2))

expect(versions.len()).to_equal(1000)
expect(base.work).to_equal(1000)
expect(versions[0].work).to_equal(1001)
```

</details>

### Edge cases

#### contains checks membership

1. expect true
2. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.from_array([1, 2, 3])
expect_true(vec.contains(2))
expect_true(not vec.contains(99))
```

</details>

#### handles empty conversions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vec = MiniVec.new()
expect(vec.to_array()).to_equal([])
```

</details>

### Correctness after many operations

#### maintains correctness through mixed operations

1. var vec = MiniVec new
2. vec = vec push
3. vec = vec set
4. vec = vec pop
5. expect len
   - Expected: vec.get(i) equals `Some(i * 2)`
   - Expected: vec.get(i) equals `Some(i)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vec = MiniVec.new()

for i in 0..100:
    vec = vec.push(i)

for i in 0..50:
    vec = vec.set(i, i * 2)

for _ in 0..25:
    vec = vec.pop()

expect_len(vec, 75)
for i in 0..50:
    expect(vec.get(i)).to_equal(Some(i * 2))
for i in 50..75:
    expect(vec.get(i)).to_equal(Some(i))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/collections/persistent_vec_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PersistentVec intensive tests
- Basic operations
- Indexing
- Immutability
- Set operation
- Pop operation
- Large vector (stress test tail buffer)
- Bulk operations
- Slicing operations
- Work accounting
- Edge cases
- Correctness after many operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
