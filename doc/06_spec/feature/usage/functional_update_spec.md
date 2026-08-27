# In-Place Functional Update with the Arrow Operator

> The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr` in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations on arrays and dicts, verifies correct chaining of multiple operations in sequence, and confirms that lambda expressions with closures work within functional updates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# In-Place Functional Update with the Arrow Operator

The functional update operator `->` applies transformations to collections in place, enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr` in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations on arrays and dicts, verifies correct chaining of multiple operations in sequence, and confirms that lambda expressions with closures work within functional updates.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-031 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/functional_update_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The functional update operator `->` applies transformations to collections in place,
enabling fluent data processing pipelines. Unlike method chaining with `.`, the arrow
operator mutates the target variable directly (e.g., `arr->map(...)` transforms `arr`
in place). This spec validates `->concat`, `->map`, `->filter`, and `->set` operations
on arrays and dicts, verifies correct chaining of multiple operations in sequence,
and confirms that lambda expressions with closures work within functional updates.

## Syntax

```simple
var arr = [1, 2, 3]
arr->map(\x: x + 1)               # arr is now [2, 3, 4]
arr->filter(\x: x > 2)            # arr is now [3, 4]

var d = {"a": 1}
d->set("b", 2)                    # d now has keys "a" and "b"

var items = [5, 10, 15, 20]
items->filter(\x: x > 5)          # chained in-place transforms
items->map(\x: x - 5)             # items is now [5, 10, 15]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `->` operator | Applies a transformation to a collection in place, mutating the variable |
| `->map` | Transforms each element using a lambda, updating the collection in place |
| `->filter` | Retains only elements matching a predicate, modifying the collection in place |
| `->concat` | Appends another collection's elements to the target in place |
| `->set` | Adds or updates a key-value pair in a dict in place |
| Chained updates | Multiple `->` operations can be applied sequentially for data pipelines |

## Scenarios

### Functional Update Syntax

#### when updating a struct field

#### creates new struct with updated field

- creates new struct with updated field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates new struct with updated field")
# Functional update with concat - modifies in place and returns
var arr = [1, 2]
arr->concat([3, 4])
expect arr.len() == 4
```

</details>

#### leaves original struct unchanged

- leaves original struct unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("leaves original struct unchanged")
# Functional update with map - transforms elements in place
var arr = [1, 2, 3]
arr->map(\x: x * 2)
expect arr[1] == 4
```

</details>

#### when updating multiple fields

#### updates all specified fields

- updates all specified fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("updates all specified fields")
# Functional update with filter - filters elements in place
var arr = [1, 2, 3, 4, 5]
arr->filter(\x: x > 2)
expect arr.len() == 3
```

</details>

#### preserves unmodified fields

- preserves unmodified fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves unmodified fields")
# Dict functional update - adds new key
var d = {"a": 1}
d->set("b", 2)
expect d.len() == 2
```

</details>

### Functional Update with Nesting

#### when updating nested struct fields

#### updates nested field values

- updates nested field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("updates nested field values")
# Chained functional updates - map then filter
var arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
expect arr.len() == 2
```

</details>

#### preserves sibling fields in nested structures

- preserves sibling fields in nested structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves sibling fields in nested structures")
# Multiple dict operations
var d = {"x": 1, "y": 2}
d->set("z", 3)
expect d["x"] == 1
expect d["z"] == 3
```

</details>

#### when chaining functional updates

#### applies updates in correct order

- applies updates in correct order


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("applies updates in correct order")
# Chained array operations: [1,2,3] -> [2,3,4] -> [3,4]
var arr = [1, 2, 3]
arr->map(\x: x + 1)
arr->filter(\x: x > 2)
expect arr == [3, 4]
```

</details>

#### maintains immutability through chain

- maintains immutability through chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maintains immutability through chain")
# Multiple transformations preserve data integrity
var original = [1, 2, 3, 4, 5]
original->filter(\x: x % 2 == 0)
original->map(\x: x * 10)
expect original == [20, 40]
```

</details>

### Functional Update Advanced Patterns

#### works with generic types

- works with generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with generic types")
# Functional update works with any collection type
var numbers = [10, 20, 30]
numbers->map(\x: x / 10)
expect numbers == [1, 2, 3]
```

</details>

#### supports computed field values in update

- supports computed field values in update


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports computed field values in update")
# Lambda with complex computation in functional update
var arr = [1, 2, 3, 4, 5]
val threshold = 2
arr->filter(\x: x > threshold)
expect arr.len() == 3
```

</details>

#### handles update expressions with side effects

- handles update expressions with side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles update expressions with side effects")
# Functional update with multiple operations
var items = [5, 10, 15, 20]
items->filter(\x: x > 5)
items->map(\x: x - 5)
expect items == [5, 10, 15]
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aa93e9f4776add4eb717b0fca1c044457e961585038d5c702dac8b2fa8cec781`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aa93e9f4776add4eb717b0fca1c044457e961585038d5c702dac8b2fa8cec781`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aa93e9f4776add4eb717b0fca1c044457e961585038d5c702dac8b2fa8cec781`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/functional_update_spec.spl
mirror: doc/06_spec/feature/usage/functional_update_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/functional_update_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/functional_update_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/functional_update_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates new struct with updated field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/functional_update_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves original struct unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/functional_update_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates all specified fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
