# Mutable Collections by Default

> Simple follows the design decision that collections (arrays and dicts) are mutable by default, consistent with Python, JavaScript, and Java. Variables declared with `var` can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on arrays and dicts without any special annotation. Even `val` bindings to collections allow mutation of the collection contents (the binding is immutable, not the data). This spec comprehensively validates all mutation operations on arrays and dicts, sequential borrow patterns (read after write), and edge cases like empty collections.

<!-- sdn-diagram:id=mutable_by_default_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mutable_by_default_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mutable_by_default_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mutable_by_default_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mutable Collections by Default

Simple follows the design decision that collections (arrays and dicts) are mutable by default, consistent with Python, JavaScript, and Java. Variables declared with `var` can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on arrays and dicts without any special annotation. Even `val` bindings to collections allow mutation of the collection contents (the binding is immutable, not the data). This spec comprehensively validates all mutation operations on arrays and dicts, sequential borrow patterns (read after write), and edge cases like empty collections.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-024 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/mutable_by_default_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple follows the design decision that collections (arrays and dicts) are mutable by
default, consistent with Python, JavaScript, and Java. Variables declared with `var`
can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on
arrays and dicts without any special annotation. Even `val` bindings to collections
allow mutation of the collection contents (the binding is immutable, not the data).
This spec comprehensively validates all mutation operations on arrays and dicts,
sequential borrow patterns (read after write), and edge cases like empty collections.

## Syntax

```simple
var arr = [1, 2, 3]
arr.push(4)                # append element
arr.pop()                  # remove and return last
arr.insert(1, 2)           # insert at index
arr.remove(0)              # remove at index
arr[1] = 10                # index assignment
arr.clear()                # remove all elements

var dict = {"a": 1}
dict["b"] = 2              # add new key
dict["a"] = 10             # update existing key
dict.remove("a")           # remove key
dict.clear()               # remove all entries
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Mutable by default | Arrays and dicts support mutation without explicit mutability annotations |
| `var` vs `val` binding | `var` allows rebinding; `val` prevents rebinding but both allow collection mutation |
| Array mutations | `push`, `pop`, `insert`, `remove`, `clear`, and index assignment |
| Dict mutations | Key assignment (`dict[k] = v`), `remove`, and `clear` |
| Sequential borrows | Reading after writing (e.g., `arr.push(4)` then `arr[3]`) works correctly |
| Empty collection edge cases | Pushing to `[]`, popping from `[1]`, inserting into `{}` all behave correctly |

## Scenarios

### Mutable Collections by Default

#### Array Mutability

#### allows push on default arrays

1. arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
expect arr[3] == 4
expect arr.len() == 4
```

</details>

#### allows pop on default arrays

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val last = arr.pop()
expect last == 3
expect arr.len() == 2
```

</details>

#### allows multiple pops

1. arr pop
2. arr pop
3. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
arr.pop()
arr.pop()
expect arr[2] == 3
expect arr.len() == 3
```

</details>

#### allows insert on default arrays

1. arr insert
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 3]
arr.insert(1, 2)
expect arr[1] == 2
expect arr.len() == 3
```

</details>

#### allows insert at beginning

1. arr insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [2, 3]
arr.insert(0, 1)
expect arr[0] == 1
```

</details>

#### allows insert at end

1. arr insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2]
arr.insert(2, 3)
expect arr[2] == 3
```

</details>

#### allows remove on default arrays

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val removed = arr.remove(1)
expect removed == 2
expect arr.len() == 2
```

</details>

#### allows remove first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val removed = arr.remove(0)
expect removed == 1
expect arr[0] == 2
```

</details>

#### allows remove last element

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val removed = arr.remove(2)
expect removed == 3
expect arr.len() == 2
```

</details>

#### allows clear on default arrays

1. arr clear
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.clear()
expect arr.len() == 0
```

</details>

#### allows indexing assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr[1] = 10
expect arr[1] == 10
```

</details>

#### allows indexing assignment at boundaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr[0] = 10
arr[2] = 30
expect arr[0] == 10
expect arr[2] == 30
```

</details>

#### Dict Mutability

#### allows insert on default dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

#### allows update existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1}
dict["a"] = 10
expect dict["a"] == 10
```

</details>

#### allows remove on default dicts

1. dict remove
2. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1, "b": 2}
dict.remove("a")
expect dict.len() == 1
```

</details>

#### allows clear on default dicts

1. dict clear
2. expect dict len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {"a": 1, "b": 2}
dict.clear()
expect dict.len() == 0
```

</details>

#### var binding with mutable collection

#### allows mutation with var binding

1. arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
expect arr[3] == 4
expect arr.len() == 4
```

</details>

#### allows pop with var binding

1. arr pop
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.pop()
expect arr.len() == 2
```

</details>

#### works with dict and val binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

#### Sequential operations

#### handles sequential borrows

1. arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
val len = arr.len()
expect len == 3
arr.push(4)
expect arr.len() == 4
```

</details>

#### allows read after write

1. arr push


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
val last = arr[3]
expect last == 4
```

</details>

#### Empty collection mutations

#### allows push to empty array

1. arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
arr.push(1)
expect arr[0] == 1
expect arr.len() == 1
```

</details>

#### handles pop from singleton

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1]
val elem = arr.pop()
expect elem == 1
expect arr.len() == 0
```

</details>

#### allows insert into empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict = {}
dict["key"] = "value"
expect dict["key"] == "value"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
