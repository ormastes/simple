# Mutable Collections by Default

> Simple follows the design decision that collections (arrays and dicts) are mutable by default, consistent with Python, JavaScript, and Java. Variables declared with `var` can freely `push`, `pop`, `insert`, `remove`, `clear`, and use index assignment on arrays and dicts without any special annotation. Even `val` bindings to collections allow mutation of the collection contents (the binding is immutable, not the data). This spec comprehensively validates all mutation operations on arrays and dicts, sequential borrow patterns (read after write), and edge cases like empty collections.

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
| Updated | 2026-08-26 |
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

- allows push on default arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows push on default arrays")
var arr = [1, 2, 3]
arr.push(4)
expect arr[3] == 4
expect arr.len() == 4
```

</details>

#### allows pop on default arrays

- allows pop on default arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows pop on default arrays")
var arr = [1, 2, 3]
val last = arr.pop()
expect last == 3
expect arr.len() == 2
```

</details>

#### allows multiple pops

- allows multiple pops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple pops")
var arr = [1, 2, 3, 4, 5]
arr.pop()
arr.pop()
expect arr[2] == 3
expect arr.len() == 3
```

</details>

#### allows insert on default arrays

- allows insert on default arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows insert on default arrays")
var arr = [1, 3]
arr.insert(1, 2)
expect arr[1] == 2
expect arr.len() == 3
```

</details>

#### allows insert at beginning

- allows insert at beginning


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows insert at beginning")
var arr = [2, 3]
arr.insert(0, 1)
expect arr[0] == 1
```

</details>

#### allows insert at end

- allows insert at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows insert at end")
var arr = [1, 2]
arr.insert(2, 3)
expect arr[2] == 3
```

</details>

#### allows remove on default arrays

- allows remove on default arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows remove on default arrays")
var arr = [1, 2, 3]
val removed = arr.remove(1)
expect removed == 2
expect arr.len() == 2
```

</details>

#### allows remove first element

- allows remove first element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows remove first element")
var arr = [1, 2, 3]
val removed = arr.remove(0)
expect removed == 1
expect arr[0] == 2
```

</details>

#### allows remove last element

- allows remove last element


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows remove last element")
var arr = [1, 2, 3]
val removed = arr.remove(2)
expect removed == 3
expect arr.len() == 2
```

</details>

#### allows clear on default arrays

- allows clear on default arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows clear on default arrays")
var arr = [1, 2, 3]
arr.clear()
expect arr.len() == 0
```

</details>

#### allows indexing assignment

- allows indexing assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows indexing assignment")
var arr = [1, 2, 3]
arr[1] = 10
expect arr[1] == 10
```

</details>

#### allows indexing assignment at boundaries

- allows indexing assignment at boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows indexing assignment at boundaries")
var arr = [1, 2, 3]
arr[0] = 10
arr[2] = 30
expect arr[0] == 10
expect arr[2] == 30
```

</details>

#### Dict Mutability

#### allows insert on default dicts

- allows insert on default dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows insert on default dicts")
var dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

#### allows update existing key

- allows update existing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows update existing key")
var dict = {"a": 1}
dict["a"] = 10
expect dict["a"] == 10
```

</details>

#### allows remove on default dicts

- allows remove on default dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows remove on default dicts")
var dict = {"a": 1, "b": 2}
dict.remove("a")
expect dict.len() == 1
```

</details>

#### allows clear on default dicts

- allows clear on default dicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows clear on default dicts")
var dict = {"a": 1, "b": 2}
dict.clear()
expect dict.len() == 0
```

</details>

#### var binding with mutable collection

#### allows mutation with var binding

- allows mutation with var binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows mutation with var binding")
var arr = [1, 2, 3]
arr.push(4)
expect arr[3] == 4
expect arr.len() == 4
```

</details>

#### allows pop with var binding

- allows pop with var binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows pop with var binding")
var arr = [1, 2, 3]
arr.pop()
expect arr.len() == 2
```

</details>

#### works with dict and val binding

- works with dict and val binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with dict and val binding")
val dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

#### Sequential operations

#### handles sequential borrows

- handles sequential borrows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles sequential borrows")
var arr = [1, 2, 3]
val len = arr.len()
expect len == 3
arr.push(4)
expect arr.len() == 4
```

</details>

#### allows read after write

- allows read after write


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows read after write")
var arr = [1, 2, 3]
arr.push(4)
val last = arr[3]
expect last == 4
```

</details>

#### Empty collection mutations

#### allows push to empty array

- allows push to empty array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows push to empty array")
var arr = []
arr.push(1)
expect arr[0] == 1
expect arr.len() == 1
```

</details>

#### handles pop from singleton

- handles pop from singleton


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles pop from singleton")
var arr = [1]
val elem = arr.pop()
expect elem == 1
expect arr.len() == 0
```

</details>

#### allows insert into empty dict

- allows insert into empty dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows insert into empty dict")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b53dd59c7aafb06f341cd5b336bc793764d3fb916c065dd1c0684fbcc594b76f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b53dd59c7aafb06f341cd5b336bc793764d3fb916c065dd1c0684fbcc594b76f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b53dd59c7aafb06f341cd5b336bc793764d3fb916c065dd1c0684fbcc594b76f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/mutable_by_default_spec.spl
mirror: doc/06_spec/03_system/feature/usage/mutable_by_default_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/mutable_by_default_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/mutable_by_default_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/mutable_by_default_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows push on default arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/mutable_by_default_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows pop on default arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/mutable_by_default_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows multiple pops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
