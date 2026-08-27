# Collection Utilities Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Utilities Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-UTIL-001 to #COLL-UTIL-052 |
| Category | Runtime \| Collections |
| Status | Implemented |
| Source | `test/03_system/feature/usage/collection_utilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Array Utility Methods

```simple
# Sorting (returns new array)
use std.spec.step

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sort returns new sorted array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sort returns new sorted array")
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

- sorted returns new sorted array


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorted returns new sorted array")
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

- reverse returns new reversed array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reverse returns new reversed array")
val arr = [1, 2, 3]
val r = arr.reverse()
expect r[0] == 3
expect r[1] == 2
expect r[2] == 1
```

</details>

#### reversed returns new reversed array

- reversed returns new reversed array


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reversed returns new reversed array")
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

- first returns first element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("first returns first element")
val arr = [10, 20, 30]
expect arr.first() == 10
```

</details>

#### last returns last element

- last returns last element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("last returns last element")
val arr = [10, 20, 30]
expect arr.last() == 30
```

</details>

#### first returns nil for empty array

- first returns nil for empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("first returns nil for empty array")
val arr: [i64] = []
expect arr.first() == nil
```

</details>

#### last returns nil for empty array

- last returns nil for empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("last returns nil for empty array")
val arr: [i64] = []
expect arr.last() == nil
```

</details>

#### index_of finds element

- index_of finds element


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("index_of finds element")
val arr = [10, 20, 30, 20]
expect arr.index_of(20) == 1  # First occurrence
```

</details>

#### index_of returns -1 when not found

- index_of returns -1 when not found


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("index_of returns -1 when not found")
val arr = [10, 20, 30]
expect arr.index_of(99) == -1
```

</details>

### Array Concatenation and Copy

#### concatenates two arrays

- concatenates two arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenates two arrays")
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

- creates shallow copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates shallow copy")
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

- sums numeric array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums numeric array")
val arr = [1, 2, 3, 4]
expect arr.sum() == 10
```

</details>

#### sum of empty array is zero

- sum of empty array is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sum of empty array is zero")
val arr: [i64] = []
expect arr.sum() == 0
```

</details>

#### finds minimum value

- finds minimum value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds minimum value")
val arr = [3, 1, 4, 1, 5]
expect arr.min() == 1
```

</details>

#### finds maximum value

- finds maximum value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds maximum value")
val arr = [3, 1, 4, 1, 5]
expect arr.max() == 5
```

</details>

#### min of empty array is nil

- min of empty array is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("min of empty array is nil")
val arr: [i64] = []
expect arr.min() == nil
```

</details>

#### max of empty array is nil

- max of empty array is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("max of empty array is nil")
val arr: [i64] = []
expect arr.max() == nil
```

</details>

#### counts occurrences

- counts occurrences


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts occurrences")
val arr = [1, 2, 1, 3, 1]
expect arr.count_of(1) == 3
expect arr.count_of(2) == 1
expect arr.count_of(99) == 0
```

</details>

### Array Transformation

#### zips two arrays into tuples

- zips two arrays into tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zips two arrays into tuples")
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

- enumerates array with indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enumerates array with indices")
val arr = [10, 20, 30]
val e = arr.enumerate()
expect e[0] == (0, 10)
expect e.len() == 3
expect e[1] == (1, 20)
expect e[2] == (2, 30)
```

</details>

#### flattens nested arrays

- flattens nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flattens nested arrays")
val nested = [[1, 2], [3, 4], [5]]
val result = nested.flatten()
expect result[0] == 1
expect result.len() == 5
expect result[2] == 3
expect result[4] == 5
```

</details>

#### removes duplicates

- removes duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes duplicates")
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

- takes first n elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("takes first n elements")
val arr = [1, 2, 3, 4, 5]
val t = arr.take(3)
expect t[0] == 1
expect t.len() == 3
expect t[2] == 3
```

</details>

#### drops first n elements

- drops first n elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drops first n elements")
val arr = [1, 2, 3, 4, 5]
val d = arr.drop(2)
expect d[0] == 3
expect d.len() == 3
expect d[2] == 5
```

</details>

### Array Predicates

#### all_truthy returns true when all truthy

- all_truthy returns true when all truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all_truthy returns true when all truthy")
val arr = [1, 2, 3]
expect arr.all_truthy()
```

</details>

#### all_truthy returns false with zero

- all_truthy returns false with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all_truthy returns false with zero")
val arr = [1, 0, 3]
expect not arr.all_truthy()
```

</details>

#### any_truthy returns true with some truthy

- any_truthy returns true with some truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("any_truthy returns true with some truthy")
val arr = [0, 0, 1]
expect arr.any_truthy()
```

</details>

#### any_truthy returns false when all zero

- any_truthy returns false when all zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("any_truthy returns false when all zero")
val arr = [0, 0, 0]
expect not arr.any_truthy()
```

</details>

### Array Fill

#### fills array with value

- fills array with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fills array with value")
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

- creates tuple with specified size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates tuple with specified size")
val t = (10, 20, 30)
expect t.len() == 3
```

</details>

#### gets tuple elements by index

- gets tuple elements by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets tuple elements by index")
val t = (10, 20, 30)
expect t[0] == 10
expect t[1] == 20
expect t[2] == 30
```

</details>

#### first and last on tuple

- first and last on tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("first and last on tuple")
val t = (10, 20, 30)
expect t.first() == 10
expect t.last() == 30
```

</details>

### String Operations

#### creates string and gets length

- creates string and gets length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates string and gets length")
val s = "Hello, World!"
expect s.len() == 13
```

</details>

#### concatenates strings

- concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenates strings")
val a = "Hello"
val b = " World"
val c = a + b
expect c == "Hello World"
expect c.len() == 11
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty string")
val s = ""
expect s.len() == 0
```

</details>

### Dictionary Operations

#### creates empty dict

- creates empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates empty dict")
val d = {}
expect d.len() == 0
```

</details>

#### sets and gets values

- sets and gets values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets and gets values")
var d = {}
d["name"] = "Alice"
d["age"] = 30
expect d.len() == 2
expect d["age"] == 30
```

</details>

#### overwrites existing key

- overwrites existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overwrites existing key")
var d = {"counter": 1}
d["counter"] = 2
expect d.len() == 1
expect d["counter"] == 2
```

</details>

#### returns nil for missing key

- returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for missing key")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd0eb241a6fbd320b7fbe70ab171003acfb5d179c80d4c4c304e7f912a5db27f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd0eb241a6fbd320b7fbe70ab171003acfb5d179c80d4c4c304e7f912a5db27f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd0eb241a6fbd320b7fbe70ab171003acfb5d179c80d4c4c304e7f912a5db27f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/collection_utilities_spec.spl
mirror: doc/06_spec/03_system/feature/usage/collection_utilities_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/collection_utilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/collection_utilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/collection_utilities_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sort returns new sorted array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/collection_utilities_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorted returns new sorted array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/collection_utilities_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverse returns new reversed array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
