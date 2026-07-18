# Collection Utilities Specification

> val sorted = arr.sort()      # Returns new sorted array

<!-- sdn-diagram:id=collection_utilities_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collection_utilities_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collection_utilities_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collection_utilities_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Utilities Specification

val sorted = arr.sort()      # Returns new sorted array

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-UTIL-001 to #COLL-UTIL-052 |
| Category | Runtime \| Collections |
| Status | Implemented |
| Source | `test/03_system/feature/usage/collection_utilities_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Array Utility Methods

```simple
# Sorting (returns new array)
val sorted = arr.sort()      # Returns new sorted array
val sorted = arr.sorted()    # Alias for sort

# Reversing (returns new array)
val rev = arr.reverse()      # Returns new reversed array
val rev = arr.reversed()     # Alias for reverse

# Access
arr.first()             # First element or nil
arr.last()              # Last element or nil
arr.index_of(value)     # Index or -1 if not found

# Aggregation
arr.sum()               # Sum of numeric elements
arr.min()               # Minimum value or nil
arr.max()               # Maximum value or nil
arr.count_of(value)     # Count occurrences of specific value

# Transformation
arr.concat(other)       # Concatenate arrays
arr.copy()              # Shallow copy
arr.zip(other)          # Zip into tuples
arr.enumerate()         # Add indices as tuples
arr.flatten()           # Flatten nested arrays
arr.unique()            # Remove duplicates
arr.take(n)             # First n elements
arr.drop(n)             # Skip first n elements

# Predicates
arr.all_truthy()        # All elements truthy?
arr.any_truthy()        # Any element truthy?
```

## Scenarios

### Array Sorting

#### sort returns new sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 4, 1, 5]
val s = arr.sort()
expect s[0] == 1
expect s[1] == 1
expect s[2] == 3
expect s[3] == 4
expect s[4] == 5
```

</details>

#### sorted returns new sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 2]
val s = arr.sorted()
# Original unchanged
expect arr[0] == 3
# New array sorted
expect s[0] == 1
expect s[1] == 2
expect s[2] == 3
```

</details>

### Array Reversing

#### reverse returns new reversed array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val r = arr.reverse()
expect r[0] == 3
expect r[1] == 2
expect r[2] == 1
```

</details>

#### reversed returns new reversed array

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val r = arr.reversed()
# Original unchanged
expect arr[0] == 1
# New array reversed
expect r[0] == 3
expect r[1] == 2
expect r[2] == 1
```

</details>

### Array Access Methods

#### first returns first element

1. expect arr first


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr.first() == 10
```

</details>

#### last returns last element

1. expect arr last


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr.last() == 30
```

</details>

#### first returns nil for empty array

1. expect arr first


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr.first() == nil
```

</details>

#### last returns nil for empty array

1. expect arr last


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr.last() == nil
```

</details>

#### index_of finds element

1. expect arr index of


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30, 20]
expect arr.index_of(20) == 1  # First occurrence
```

</details>

#### index_of returns -1 when not found

1. expect arr index of


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect arr.index_of(99) == -1
```

</details>

### Array Concatenation and Copy

#### concatenates two arrays

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2]
val b = [3, 4]
val c = a.concat(b)
expect c[0] == 1
expect c.len() == 4
expect c[2] == 3
expect c[3] == 4
```

</details>

#### creates shallow copy

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val c = arr.copy()
expect c[0] == 1
expect c.len() == 3
expect c[1] == 2
expect c[2] == 3
```

</details>

### Array Aggregation

#### sums numeric array

1. expect arr sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4]
expect arr.sum() == 10
```

</details>

#### sum of empty array is zero

1. expect arr sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr.sum() == 0
```

</details>

#### finds minimum value

1. expect arr min


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 4, 1, 5]
expect arr.min() == 1
```

</details>

#### finds maximum value

1. expect arr max


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [3, 1, 4, 1, 5]
expect arr.max() == 5
```

</details>

#### min of empty array is nil

1. expect arr min


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr.min() == nil
```

</details>

#### max of empty array is nil

1. expect arr max


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
expect arr.max() == nil
```

</details>

#### counts occurrences

1. expect arr count of
2. expect arr count of
3. expect arr count of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 1, 3, 1]
expect arr.count_of(1) == 3
expect arr.count_of(2) == 1
expect arr.count_of(99) == 0
```

</details>

### Array Transformation

#### zips two arrays into tuples

1. expect z[0] ==
2. expect z len
3. expect z[1] ==
4. expect z[2] ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = [10, 20, 30]
val z = a.zip(b)
expect z[0] == (1, 10)
expect z.len() == 3
expect z[1] == (2, 20)
expect z[2] == (3, 30)
```

</details>

#### enumerates array with indices

1. expect e[0] ==
2. expect e len
3. expect e[1] ==
4. expect e[2] ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val e = arr.enumerate()
expect e[0] == (0, 10)
expect e.len() == 3
expect e[1] == (1, 20)
expect e[2] == (2, 30)
```

</details>

#### flattens nested arrays

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [[1, 2], [3, 4], [5]]
val result = nested.flatten()
expect result[0] == 1
expect result.len() == 5
expect result[2] == 3
expect result[4] == 5
```

</details>

#### removes duplicates

1. expect u len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 1, 3, 2, 1]
val u = arr.unique()
expect u[0] == 1
expect u.len() == 3
expect u[1] == 2
expect u[2] == 3
```

</details>

### Array Slicing Methods

#### takes first n elements

1. expect t len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
val t = arr.take(3)
expect t[0] == 1
expect t.len() == 3
expect t[2] == 3
```

</details>

#### drops first n elements

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
val d = arr.drop(2)
expect d[0] == 3
expect d.len() == 3
expect d[2] == 5
```

</details>

### Array Predicates

#### all_truthy returns true when all truthy

1. expect arr all truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr.all_truthy()
```

</details>

#### all_truthy returns false with zero

1. expect not arr all truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 0, 3]
expect not arr.all_truthy()
```

</details>

#### any_truthy returns true with some truthy

1. expect arr any truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 0, 1]
expect arr.any_truthy()
```

</details>

#### any_truthy returns false when all zero

1. expect not arr any truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 0, 0]
expect not arr.any_truthy()
```

</details>

### Array Fill

#### fills array with value

1. expect filled len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val filled = arr.fill(0)
expect filled[0] == 0
expect filled.len() == 3
expect filled[1] == 0
expect filled[2] == 0
```

</details>

### Tuple Operations

#### creates tuple with specified size

1. expect t len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 30)
expect t.len() == 3
```

</details>

#### gets tuple elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 30)
expect t[0] == 10
expect t[1] == 20
expect t[2] == 30
```

</details>

#### first and last on tuple

1. expect t first
2. expect t last


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 30)
expect t.first() == 10
expect t.last() == 30
```

</details>

### String Operations

#### creates string and gets length

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello, World!"
expect s.len() == 13
```

</details>

#### concatenates strings

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "Hello"
val b = " World"
val c = a + b
expect c == "Hello World"
expect c.len() == 11
```

</details>

#### handles empty string

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
expect s.len() == 0
```

</details>

### Dictionary Operations

#### creates empty dict

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {}
expect d.len() == 0
```

</details>

#### sets and gets values

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {}
d["name"] = "Alice"
d["age"] = 30
expect d.len() == 2
expect d["age"] == 30
```

</details>

#### overwrites existing key

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"counter": 1}
d["counter"] = 2
expect d.len() == 1
expect d["counter"] == 2
```

</details>

#### returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1}
expect d["missing"] == nil
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
