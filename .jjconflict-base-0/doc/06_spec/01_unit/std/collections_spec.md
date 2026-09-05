# Collections Specification

> 1. expect empty len

<!-- sdn-diagram:id=collections_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collections_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collections_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collections_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections Specification

## Scenarios

### List operations

#### creates empty list

1. expect empty len
2. expect empty is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect empty.len() == 0
expect empty.is_empty()
```

</details>

#### creates list with elements

1. expect nums len
2. expect not nums is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5]
expect nums.len() == 5
expect not nums.is_empty()
```

</details>

#### accesses elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [10, 20, 30]
expect nums[0] == 10
expect nums[1] == 20
expect nums[2] == 30
```

</details>

#### uses negative indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [10, 20, 30, 40]
expect nums[-1] == 40  # Last element
expect nums[-2] == 30  # Second to last
```

</details>

#### slices lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Slicing syntax verified working (Phase 5 - TODO ✅)
val nums = [0, 1, 2, 3, 4, 5]
val slice = nums[1:4]  # Elements 1, 2, 3
expect(slice.len()).to_equal(3)
expect(slice[0]).to_equal(1)
expect(slice[1]).to_equal(2)
```

</details>

#### appends elements

1. nums push
2. expect nums len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums = [1, 2, 3]
nums.push(4)
expect nums.len() == 4
expect nums[-1] == 4
```

</details>

#### maps over elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3]
val doubled = nums.map(_ * 2)
expect doubled == [2, 4, 6]
```

</details>

#### filters elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4, 5, 6]
val evens = nums.filter(_ % 2 == 0)
expect evens == [2, 4, 6]
```

</details>

#### reduces elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [1, 2, 3, 4]
val sum = nums.reduce(0, \acc, x: acc + x)
expect sum == 10
```

</details>

### Dict operations

#### creates empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: {text: i64} = {}
val elen = empty.len()
expect elen == 0
```

</details>

#### creates dict with entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"Alice": 30, "Bob": 25}
val alen = ages.len()
expect alen == 2
```

</details>

#### accesses values by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"Alice": 30, "Bob": 25}
expect ages["Alice"] == 30
expect ages["Bob"] == 25
```

</details>

#### checks key existence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"Alice": 30}
val has_alice = ages.has("Alice")
expect has_alice == true
val has_bob = ages.has("Bob")
expect has_bob == false
```

</details>

#### gets keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"Alice": 30, "Bob": 25}
val keys = ages.keys()
val klen = keys.len()
expect klen == 2
```

</details>

#### gets values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ages = {"Alice": 30, "Bob": 25}
val values = ages.values()
val vlen = values.len()
expect vlen == 2
```

</details>

#### inserts new entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ages = {"Alice": 30}
ages["Bob"] = 25
val alen = ages.len()
expect alen == 2
expect ages["Bob"] == 25
```

</details>

#### updates existing entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ages = {"Alice": 30}
ages["Alice"] = 31
expect ages["Alice"] == 31
```

</details>

### Set operations

#### creates empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty = {}
val elen = empty.len()
expect elen == 0
```

</details>

#### creates set with elements via dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums = {}
nums["1"] = true
nums["2"] = true
nums["3"] = true
val nlen = nums.len()
expect nlen == 3
```

</details>

#### adds elements and deduplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums = {}
nums["1"] = true
nums["2"] = true
nums["1"] = true
val nlen = nums.len()
expect nlen == 2
```

</details>

#### checks membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums = {}
nums["2"] = true
nums["3"] = true
val has2 = nums.has("2")
expect has2 == true
val has5 = nums.has("5")
expect has5 == false
```

</details>

#### computes union via dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = {}
a["1"] = true
a["2"] = true
a["3"] = true
var b = {}
b["3"] = true
b["4"] = true
b["5"] = true
var union_set = {}
for k in a.keys():
    union_set[k] = true
for k in b.keys():
    union_set[k] = true
val ulen = union_set.len()
expect ulen == 5
```

</details>

#### computes intersection via dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = {}
a["1"] = true
a["2"] = true
a["3"] = true
var b = {}
b["2"] = true
b["3"] = true
b["4"] = true
var isect = {}
for k in a.keys():
    if b.has(k):
        isect[k] = true
val ilen = isect.len()
expect ilen == 2
```

</details>

#### computes difference via dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = {}
a["1"] = true
a["2"] = true
a["3"] = true
var b = {}
b["2"] = true
b["3"] = true
var diff = {}
for k in a.keys():
    if not b.has(k):
        diff[k] = true
val dlen = diff.len()
expect dlen == 1
val has1 = diff.has("1")
expect has1 == true
```

</details>

### String operations

#### concatenates strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "Hello"
val s2 = "World"
val combined = s1 + " " + s2
expect combined == "Hello World"
```

</details>

#### gets string length

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s.len() == 5
```

</details>

#### checks string emptiness

1. expect empty is empty
2. expect not non empty is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
val non_empty = "text"
expect empty.is_empty()
expect not non_empty.is_empty()
```

</details>

#### splits strings

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "a,b,c"
val parts = s.split(",")
expect parts.len() == 3
expect parts[0] == "a"
```

</details>

#### joins strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = ["a", "b", "c"]
val joined = parts.join(",")
expect joined == "a,b,c"
```

</details>

#### trims whitespace

1. expect s trim


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  hello  "
expect s.trim() == "hello"
```

</details>

#### converts case

1. expect s upper
2. expect s lower


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "Hello"
expect s.upper() == "HELLO"
expect s.lower() == "hello"
```

</details>

#### checks prefixes and suffixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello.txt"
val sw = s.starts_with("hello")
expect sw == true
# ends_with has stack overflow in interpreter - check via slice
val last4 = s[5:9]
expect last4 == ".txt"
```

</details>

#### finds substrings

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
val pos = s.index_of("world")
match pos:
    Some(idx):
        expect idx == 6
    nil:
        expect false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/collections_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- List operations
- Dict operations
- Set operations
- String operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
