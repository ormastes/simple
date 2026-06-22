# Dictionary Types Specification

> Tests for dictionary (map) types and their operations.

<!-- sdn-diagram:id=dictionary_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dictionary_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dictionary_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dictionary_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dictionary Types Specification

Tests for dictionary (map) types and their operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1002 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/dictionary_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for dictionary (map) types and their operations.
Verifies dictionary creation, access, modification, and iteration.

## Scenarios

### Dictionary Types

#### dictionary creation

#### creates empty dictionary

1. expect empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: Dict<text, i32> = {}
expect empty.len() == 0
```

</details>

#### creates dictionary with initial values

1. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
expect dict.len() == 3
```

</details>

#### creates dictionary with string keys and values

1. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"name": "Alice", "city": "NYC"}
expect dict.len() == 2
```

</details>

#### dictionary access

#### retrieves value by key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2}
expect dict["a"] == 1
```

</details>

#### returns null for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1}
val value = dict.get("missing")
expect value == nil
```

</details>

#### checks key existence

1. expect dict contains
2. expect dict contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2}
expect dict.contains("a") == true
expect dict.contains("c") == false
```

</details>

#### dictionary modification

#### adds new key-value pair

1. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
expect dict.len() == 2
```

</details>

#### updates existing value

1. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
dict["a"] = 10
expect dict["a"] == 10
expect dict.len() == 1
```

</details>

#### removes entry by key

1. dict remove
2. expect dict contains
3. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1, "b": 2}
dict.remove("a")
expect dict.contains("a") == false
expect dict.len() == 1
```

</details>

#### dictionary iteration

#### iterates over keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
var count = 0
for key in dict.keys():
    count = count + 1
expect count == 3
```

</details>

#### iterates over values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
var sum = 0
for value in dict.values():
    sum = sum + value
expect sum == 6
```

</details>

#### iterates over entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2}
var count = 0
for entry in dict:
    count = count + 1
expect count == 2
```

</details>

#### dictionary methods

#### gets dictionary size

1. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1, "b": 2, "c": 3}
expect dict.len() == 3
```

</details>

#### checks if dictionary is empty

1. expect empty is empty
2. expect full is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: Dict<text, i32> = {}
val full = {"a": 1}
expect empty.is_empty() == true
expect full.is_empty() == false
```

</details>

#### clears dictionary

1. dict clear
2. expect dict len
3. expect dict is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1, "b": 2}
dict.clear()
expect dict.len() == 0
expect dict.is_empty() == true
```

</details>

#### creates copy of dictionary

1. expect copy len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = {"a": 1, "b": 2}
val copy = original.clone()
expect copy["a"] == 1
expect copy.len() == original.len()
```

</details>

#### dictionary with multiple types

#### stores different value types

1. expect mixed len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = {"int": 1, "text": "hello", "float": 3.14}
expect mixed.len() == 3
```

</details>

#### accesses values with correct types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"count": 5}
val value = dict["count"]
expect value == 5
```

</details>

### Functional Dictionary Methods

#### set and merge

#### sets key with functional update

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = {"a": 1}
d["b"] = 2
expect d["b"] == 2
```

</details>

#### merges two dictionaries

1. d1 = d1 merge
2. expect d1 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d1 = {"a": 1}
val d2 = {"b": 2}
d1 = d1.merge(d2)
expect d1.len() == 2
```

</details>

#### get with default

#### gets value or default

1. expect d get or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 10}
expect d.get_or("b", 99) == 99
```

</details>

#### gets existing value instead of default

1. expect d get or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 10}
expect d.get_or("a", 99) == 10
```

</details>

### Dictionary Comprehension

#### creates dict from comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val d = {x: x * x for x in arr}
expect d[2] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
