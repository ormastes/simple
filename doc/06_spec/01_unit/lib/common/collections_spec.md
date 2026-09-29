# Collections Specification

> Tests covering Option Type, Result Type, Array Type, List Type, Dictionary (Dict) Type.

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

- creates Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Some value")
val opt = Some(42)
expect opt.is_some == true
```

</details>

#### creates None value

- creates None value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates None value")
val opt = None
expect opt.is_none == true
```

</details>

#### is_some returns true for Some

- is_some returns true for Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_some returns true for Some")
val opt = Some(10)
expect opt.is_some == true
```

</details>

#### is_none returns true for None

- is_none returns true for None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_none returns true for None")
val opt = None
expect opt.is_none == true
```

</details>

#### unwrap operations

#### unwrap extracts Some value

- unwrap extracts Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap extracts Some value")
val opt = Some(42)
expect opt.unwrap() == 42
```

</details>

#### expect returns value with message

- expect returns value with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expect returns value with message")
val opt = Some(99)
expect opt.expect("Should have value") == 99
```

</details>

#### unwrap_or returns default for None

- unwrap_or returns default for None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_or returns default for None")
val opt = None
expect opt.unwrap_or(0) == 0
```

</details>

#### unwrap_or returns Some value

- unwrap_or returns Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_or returns Some value")
val opt = Some(5)
expect opt.unwrap_or(0) == 5
```

</details>

#### or and conversion

#### or returns self if Some

- or returns self if Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or returns self if Some")
val opt1 = Some(1)
val opt2 = Some(2)
expect opt1.or(opt2).unwrap() == 1
```

</details>

#### or returns other if None

- or returns other if None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or returns other if None")
val opt1 = None
val opt2 = Some(2)
expect opt1.or(opt2).unwrap() == 2
```

</details>

#### ok_or converts Some to Ok

- ok_or converts Some to Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok_or converts Some to Ok")
val opt = Some(42)
val res_obj = opt.ok_or("error")
expect res_obj.is_ok == true
```

</details>

#### ok_or converts None to Err

- ok_or converts None to Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok_or converts None to Err")
val opt = None
val res_obj = opt.ok_or("error")
expect res_obj.is_err == true
```

</details>

### Result Type

#### creation and checks

#### creates Ok value

- creates Ok value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Ok value")
val res_obj = Ok(42)
expect res_obj.is_ok == true
```

</details>

#### creates Err value

- creates Err value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Err value")
val res_obj = Err("error")
expect res_obj.is_err == true
```

</details>

#### is_ok returns true for Ok

- is_ok returns true for Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_ok returns true for Ok")
val res_obj = Ok(10)
expect res_obj.is_ok == true
```

</details>

#### is_err returns true for Err

- is_err returns true for Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_err returns true for Err")
val res_obj = Err("error")
expect res_obj.is_err == true
```

</details>

#### unwrap operations

#### unwrap extracts Ok value

- unwrap extracts Ok value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap extracts Ok value")
val res_obj = Ok(42)
expect res_obj.unwrap() == 42
```

</details>

#### unwrap_err extracts Err value

- unwrap_err extracts Err value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_err extracts Err value")
val res_obj = Err("failure")
expect res_obj.unwrap_err() == "failure"
```

</details>

#### unwrap_or returns default for Err

- unwrap_or returns default for Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_or returns default for Err")
val res_obj = Err("error")
expect res_obj.unwrap_or(0) == 0
```

</details>

#### unwrap_or returns Ok value

- unwrap_or returns Ok value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_or returns Ok value")
val res_obj = Ok(5)
expect res_obj.unwrap_or(0) == 5
```

</details>

#### expect returns value with message

- expect returns value with message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expect returns value with message")
val res_obj = Ok(99)
expect res_obj.expect("Should succeed") == 99
```

</details>

#### or operations

#### or returns self if Ok

- or returns self if Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or returns self if Ok")
val res1 = Ok(1)
val res2 = Err("error2")
expect res1.or(res2).unwrap() == 1
```

</details>

#### or returns other if Err

- or returns other if Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or returns other if Err")
val res1 = Err("error1")
val res2 = Ok(2)
expect res1.or(res2).unwrap() == 2
```

</details>

#### conversion operations

#### ok converts Ok to Some

- ok converts Ok to Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok converts Ok to Some")
val res_obj = Ok(42)
val opt = res_obj.ok()
expect opt.is_some == true
expect opt.unwrap() == 42
```

</details>

#### ok converts Err to None

- ok converts Err to None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ok converts Err to None")
val res_obj = Err("error")
val opt = res_obj.ok()
expect opt.is_none == true
```

</details>

#### err converts Err to Some

- err converts Err to Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("err converts Err to Some")
val res_obj = Err("error")
val opt = res_obj.err()
expect opt.is_some == true
expect opt.unwrap() == "error"
```

</details>

#### err converts Ok to None

- err converts Ok to None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("err converts Ok to None")
val res_obj = Ok(42)
val opt = res_obj.err()
expect opt.is_none == true
```

</details>

### Array Type

#### creation and access

#### creates array with literals

- creates array with literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates array with literals")
var arr = [1, 2, 3, 4, 5]
expect arr.len == 5
```

</details>

#### accesses elements by index

- accesses elements by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accesses elements by index")
var arr = [10, 20, 30]
expect arr[0] == 10
expect arr[1] == 20
expect arr[2] == 30
```

</details>

#### creates empty array

- creates empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty array")
val empty = []
expect empty.len == 0
```

</details>

#### array methods

#### push adds element

- push adds element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push adds element")
# Note: push returns a new array (functional style)
var arr = [1, 2]
arr = arr.push(3)
expect arr.len == 3
expect arr[2] == 3
```

</details>

#### pop removes last element

- pop removes last element


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop removes last element")
# Note: pop returns a new array without last element
var arr = [1, 2, 3]
arr = arr.pop()
expect arr.len == 2
expect arr[1] == 2
```

</details>

#### contains checks for element

- contains checks for element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains checks for element")
var arr = [1, 2, 3]
expect arr.contains(2) == true
expect arr.contains(5) == false
```

</details>

#### is_empty checks length

- is_empty checks length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_empty checks length")
val empty_arr = []
expect empty_arr.is_empty == true
val full = [1]
expect full.is_empty == false
```

</details>

### List Type

#### creation and operations

#### creates empty list

- creates empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty list")
# Try creating with array literal instead
var list = []
expect list.is_empty == true
```

</details>

#### append adds elements

- append adds elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("append adds elements")
# Using array literals - they support append operations
var list = []
list = list.push(1)
list = list.push(2)
expect list.len == 2
```

</details>

#### length tracking

- length tracking


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("length tracking")
# Using array literals - they support length operations
var list = []
expect list.len == 0
list = list.push(1)
expect list.len == 1
```

</details>

#### access elements

- access elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("access elements")
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

- contains checks membership


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains checks membership")
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

- is_empty returns correct status


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_empty returns correct status")
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

- creates empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty dict")
val dict = {}
expect dict.is_empty == true
```

</details>

#### inserts and retrieves values

- inserts and retrieves values


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts and retrieves values")
# Index assignment (dict_["key"] = value) is the correct form; it
# needs a `var` binding, hence dict_ below.
# Do NOT switch these back to `.set()`. The old comment here claimed
# ".set() returns a new dict" — that is false. Measured 2026-07-31:
# .set() MUTATES the receiver and returns an ALIAS to it (after
# `val e = d.set("b", 2)`, both d and e contain the key), and under
# native codegen it silently DROPS the insert entirely.
# See doc/07_guide/language/dict_native_pitfalls.md
var dict_ = {}
dict_["key1"] = 10
expect dict_.get("key1") == 10
```

</details>

#### checks for key existence

- checks for key existence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for key existence")
var dict_ = {}
dict_["exists"] = 1
expect dict_.contains("exists") == true
expect dict_.contains("missing") == false
```

</details>

#### counts items

- counts items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts items")
var dict_ = {}
dict_["a"] = 1
dict_["b"] = 2
expect dict_.len == 2
```

</details>

#### dict methods

#### keys returns all keys

- keys returns all keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keys returns all keys")
var dict_ = {}
dict_["x"] = 1
dict_["y"] = 2
val keys = dict_.keys()
expect keys.len == 2
```

</details>

#### values returns all values

- values returns all values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values returns all values")
var dict_ = {}
dict_["a"] = 10
dict_["b"] = 20
val values = dict_.values()
expect values.len == 2
```

</details>

#### remove deletes entries

- remove deletes entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove deletes entries")
var dict_ = {}
dict_["key"] = 1
expect dict_.len == 1
dict_ = dict_.remove("key")
expect dict_.len == 0
```

</details>

#### clear removes all entries

- clear removes all entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear removes all entries")
var dict_ = {}
dict_["a"] = 1
dict_["b"] = 2
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Option Type, Result Type, Array Type, List Type, Dictionary (Dict) Type.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5fe309ec2b91daf06f1ffd495c65c7f3992d901530a636af62c04da2915d8d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5fe309ec2b91daf06f1ffd495c65c7f3992d901530a636af62c04da2915d8d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5fe309ec2b91daf06f1ffd495c65c7f3992d901530a636af62c04da2915d8d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/collections_spec.spl
mirror: doc/06_spec/01_unit/lib/common/collections_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/collections_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/collections_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/collections_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Some value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/collections_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates None value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/collections_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_some returns true for Some' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
