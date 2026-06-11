# Collections Specification

> <details>

<!-- sdn-diagram:id=collections_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collections_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collections_spec -> test
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
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collections Specification

## Scenarios

### Option Type

#### creation and checks

#### creates Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.is_some == true
```

</details>

#### creates None value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
expect opt.is_none == true
```

</details>

#### is_some returns true for Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(10)
expect opt.is_some == true
```

</details>

#### is_none returns true for None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
expect opt.is_none == true
```

</details>

#### unwrap operations

#### unwrap extracts Some value

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.unwrap() == 42
```

</details>

#### expect returns value with message

1. expect opt expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(99)
expect opt.expect("Should have value") == 99
```

</details>

#### unwrap_or returns default for None

1. expect opt unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
expect opt.unwrap_or(0) == 0
```

</details>

#### unwrap_or returns Some value

1. expect opt unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(5)
expect opt.unwrap_or(0) == 5
```

</details>

#### or and conversion

#### or returns self if Some

1. expect opt1 or


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = Some(1)
val opt2 = Some(2)
expect opt1.or(opt2).unwrap() == 1
```

</details>

#### or returns other if None

1. expect opt1 or


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = None
val opt2 = Some(2)
expect opt1.or(opt2).unwrap() == 2
```

</details>

#### ok_or converts Some to Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val res_obj = opt.ok_or("error")
expect res_obj.is_ok == true
```

</details>

#### ok_or converts None to Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
val res_obj = opt.ok_or("error")
expect res_obj.is_err == true
```

</details>

### Result Type

#### creation and checks

#### creates Ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(42)
expect res_obj.is_ok == true
```

</details>

#### creates Err value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("error")
expect res_obj.is_err == true
```

</details>

#### is_ok returns true for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(10)
expect res_obj.is_ok == true
```

</details>

#### is_err returns true for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("error")
expect res_obj.is_err == true
```

</details>

#### unwrap operations

#### unwrap extracts Ok value

1. expect res obj unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(42)
expect res_obj.unwrap() == 42
```

</details>

#### unwrap_err extracts Err value

1. expect res obj unwrap err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("failure")
expect res_obj.unwrap_err() == "failure"
```

</details>

#### unwrap_or returns default for Err

1. expect res obj unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("error")
expect res_obj.unwrap_or(0) == 0
```

</details>

#### unwrap_or returns Ok value

1. expect res obj unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(5)
expect res_obj.unwrap_or(0) == 5
```

</details>

#### expect returns value with message

1. expect res obj expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(99)
expect res_obj.expect("Should succeed") == 99
```

</details>

#### or operations

#### or returns self if Ok

1. expect res1 or


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res1 = Ok(1)
val res2 = Err("error2")
expect res1.or(res2).unwrap() == 1
```

</details>

#### or returns other if Err

1. expect res1 or


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res1 = Err("error1")
val res2 = Ok(2)
expect res1.or(res2).unwrap() == 2
```

</details>

#### conversion operations

#### ok converts Ok to Some

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(42)
val opt = res_obj.ok()
expect opt.is_some == true
expect opt.unwrap() == 42
```

</details>

#### ok converts Err to None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("error")
val opt = res_obj.ok()
expect opt.is_none == true
```

</details>

#### err converts Err to Some

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Err("error")
val opt = res_obj.err()
expect opt.is_some == true
expect opt.unwrap() == "error"
```

</details>

#### err converts Ok to None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res_obj = Ok(42)
val opt = res_obj.err()
expect opt.is_none == true
```

</details>

### Array Type

#### creation and access

#### creates array with literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
expect arr.len == 5
```

</details>

#### accesses elements by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
expect arr[0] == 10
expect arr[1] == 20
expect arr[2] == 30
```

</details>

#### creates empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = []
expect empty.len == 0
```

</details>

#### array methods

#### push adds element

1. arr = arr push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: push returns a new array (functional style)
var arr = [1, 2]
arr = arr.push(3)
expect arr.len == 3
expect arr[2] == 3
```

</details>

#### pop removes last element

1. arr = arr pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: pop returns a new array without last element
var arr = [1, 2, 3]
arr = arr.pop()
expect arr.len == 2
expect arr[1] == 2
```

</details>

#### contains checks for element

1. expect arr contains
2. expect arr contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
expect arr.contains(2) == true
expect arr.contains(5) == false
```

</details>

#### is_empty checks length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_arr = []
expect empty_arr.is_empty == true
val full = [1]
expect full.is_empty == false
```

</details>

### List Type

#### creation and operations

#### creates empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Try creating with array literal instead
var list = []
expect list.is_empty == true
```

</details>

#### append adds elements

1. list = list push
2. list = list push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using array literals - they support append operations
var list = []
list = list.push(1)
list = list.push(2)
expect list.len == 2
```

</details>

#### length tracking

1. list = list push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using array literals - they support length operations
var list = []
expect list.len == 0
list = list.push(1)
expect list.len == 1
```

</details>

#### access elements

1. list = list push
2. list = list push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using array literals - they support indexing
var list = []
list = list.push(10)
list = list.push(20)
expect list[0] == 10
expect list[1] == 20
```

</details>

#### list methods

#### contains checks membership

1. list = list push
2. list = list push
3. list = list push
4. expect list contains
5. expect list contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using array literals - they support contains
var list = []
list = list.push(1)
list = list.push(2)
list = list.push(3)
expect list.contains(2) == true
expect list.contains(5) == false
```

</details>

#### is_empty returns correct status

1. list = list push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using array literals - they support is_empty
var list = []
expect list.is_empty == true
list = list.push(1)
expect list.is_empty == false
```

</details>

### Dictionary (Dict) Type

#### creation and operations

#### creates empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {}
expect dict.is_empty == true
```

</details>

#### inserts and retrieves values

1. dict  = dict  set
2. expect dict  get


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using functional style: dict.set() returns new dict
# Note: Index assignment (dict["key"] = value) works but
# requires mutable variable scope (use var dict_ or direct script)
var dict_ = {}
dict_ = dict_.set("key1", 10)
expect dict_.get("key1") == 10
```

</details>

#### checks for key existence

1. dict  = dict  set
2. expect dict  contains
3. expect dict  contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("exists", 1)
expect dict_.contains("exists") == true
expect dict_.contains("missing") == false
```

</details>

#### counts items

1. dict  = dict  set
2. dict  = dict  set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("a", 1)
dict_ = dict_.set("b", 2)
expect dict_.len == 2
```

</details>

#### dict methods

#### keys returns all keys

1. dict  = dict  set
2. dict  = dict  set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("x", 1)
dict_ = dict_.set("y", 2)
val keys = dict_.keys()
expect keys.len == 2
```

</details>

#### values returns all values

1. dict  = dict  set
2. dict  = dict  set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("a", 10)
dict_ = dict_.set("b", 20)
val values = dict_.values()
expect values.len == 2
```

</details>

#### remove deletes entries

1. dict  = dict  set
2. dict  = dict  remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("key", 1)
expect dict_.len == 1
dict_ = dict_.remove("key")
expect dict_.len == 0
```

</details>

#### clear removes all entries

1. dict  = dict  set
2. dict  = dict  set
3. dict  = dict  clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dict_ = {}
dict_ = dict_.set("a", 1)
dict_ = dict_.set("b", 2)
dict_ = dict_.clear()
expect dict_.is_empty == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/collections_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Option Type
- Result Type
- Array Type
- List Type
- Dictionary (Dict) Type

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
