# Placeholder Lambda Expressions

> Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive parameter. The compiler desugars `_ * 2` into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec covers the full surface area: comparison operators, arithmetic (including unary negation), method access on the placeholder (`_.len()`), chaining of `filter` and `map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`, `all`). Edge cases for empty and single-element collections are also tested.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Placeholder Lambda Expressions

Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive parameter. The compiler desugars `_ * 2` into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec covers the full surface area: comparison operators, arithmetic (including unary negation), method access on the placeholder (`_.len()`), chaining of `filter` and `map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`, `all`). Edge cases for empty and single-element collections are also tested.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-009 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/placeholder_lambda_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Placeholder lambdas let the programmer write concise anonymous functions by using
`_` as a stand-in for each successive parameter. The compiler desugars `_ * 2`
into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec
covers the full surface area: comparison operators, arithmetic (including unary
negation), method access on the placeholder (`_.len()`), chaining of `filter` and
`map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`,
`all`). Edge cases for empty and single-element collections are also tested.

## Syntax

```simple
# Filter with comparison placeholder
use std.spec.step

val evens = [1, 2, 3, 4, 5].filter(_ % 2 == 0)   # => [2, 4, 6]

# Map with arithmetic placeholder
val doubled = [1, 2, 3].map(_ * 10)                # => [10, 20, 30]

# Unary negation placeholder
val negated = [1, 2, 3].map(-_)                    # => [-1, -2, -3]

# Method call on placeholder
val long = ["hi", "hello", "hey"].filter(_.len() > 3)  # => ["hello"]

# Chained placeholders
val result = [1, 2, 3, 4, 5].filter(_ > 2).map(_ * 2)  # => [6, 8, 10]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Placeholder `_` | Each `_` in an expression becomes a new auto-named lambda parameter |
| Desugaring | `_ op expr` is rewritten to `\__pN: __pN op expr` before evaluation |
| Method access | `_.method()` desugars to `\__p0: __p0.method()` for member calls |
| Chaining | Successive `.filter(_)` and `.map(_)` calls each introduce independent lambdas |

## Scenarios

### Placeholder Lambda

#### filter with comparison

#### filters with less than

- filters with less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with less than")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ < 3)
expect result == [1, 2]
```

</details>

#### filters with greater than

- filters with greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with greater than")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 3)
expect result == [4, 5]
```

</details>

#### filters with less than or equal

- filters with less than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with less than or equal")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ <= 3)
expect result == [1, 2, 3]
```

</details>

#### filters with greater than or equal

- filters with greater than or equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with greater than or equal")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ >= 3)
expect result == [3, 4, 5]
```

</details>

#### filters with equality

- filters with equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with equality")
val data = [1, 2, 3, 2, 1]
val result = data.filter(_ == 2)
expect result == [2, 2]
```

</details>

#### filters with not equal

- filters with not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with not equal")
val data = [1, 2, 3, 2, 1]
val result = data.filter(_ != 2)
expect result == [1, 3, 1]
```

</details>

#### map with arithmetic

#### maps with multiply

- maps with multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with multiply")
val data = [1, 2, 3]
val result = data.map(_ * 10)
expect result == [10, 20, 30]
```

</details>

#### maps with add

- maps with add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with add")
val data = [1, 2, 3]
val result = data.map(_ + 100)
expect result == [101, 102, 103]
```

</details>

#### maps with subtract

- maps with subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with subtract")
val data = [10, 20, 30]
val result = data.map(_ - 5)
expect result == [5, 15, 25]
```

</details>

#### maps with negate

- maps with negate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps with negate")
val data = [1, 2, 3]
val result = data.map(-_)
expect result == [-1, -2, -3]
```

</details>

#### chaining

#### chains filter then map

- chains filter then map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains filter then map")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_ > 2).map(_ * 2)
expect result == [6, 8, 10]
```

</details>

#### chains map then filter

- chains map then filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains map then filter")
val data = [1, 2, 3, 4, 5]
val result = data.map(_ * 2).filter(_ > 5)
expect result == [6, 8, 10]
```

</details>

#### string operations

#### filters strings by length

- filters strings by length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters strings by length")
val words = ["hi", "hello", "hey", "howdy"]
val result = words.filter(_.len() > 3)
expect result == ["hello", "howdy"]
```

</details>

#### complex expressions

#### uses placeholder in modulo

- uses placeholder in modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses placeholder in modulo")
val data = [1, 2, 3, 4, 5, 6]
val result = data.filter(_ % 2 == 0)
expect result == [2, 4, 6]
```

</details>

#### uses placeholder in compound expression

- uses placeholder in compound expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses placeholder in compound expression")
val data = [1, 2, 3, 4, 5]
val result = data.map(_ * 2 + 1)
expect result == [3, 5, 7, 9, 11]
```

</details>

#### with different collection methods

#### works with any

- works with any


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with any")
val data = [1, 2, 3]
val result = data.any(_ > 2)
expect result == true
```

</details>

#### works with all

- works with all


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with all")
val data = [2, 4, 6]
val result = data.all(_ % 2 == 0)
expect result == true
```

</details>

#### works with all returning false

- works with all returning false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with all returning false")
val data = [2, 3, 6]
val result = data.all(_ % 2 == 0)
expect result == false
```

</details>

#### empty collections

#### filter on empty returns empty

- filter on empty returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filter on empty returns empty")
val data: [i64] = []
val result = data.filter(_ > 0)
expect result == []
```

</details>

#### map on empty returns empty

- map on empty returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("map on empty returns empty")
val data: [i64] = []
val result = data.map(_ * 2)
expect result == []
```

</details>

#### single element

#### filter matching single element

- filter matching single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filter matching single element")
val data = [42]
val result = data.filter(_ == 42)
expect result == [42]
```

</details>

#### filter non-matching single element

- filter non-matching single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filter non-matching single element")
val data = [42]
val result = data.filter(_ == 0)
expect result == []
```

</details>

#### string template placeholder scoping (bug wildcard_import_c_backend_stubs_function_to_int, 2026-07-30 bonus-find)

#### keeps `_` bound to the outer tuple when a template slot calls a plain function

- keeps `_` bound to the outer tuple when a template slot calls a plain function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps `_` bound to the outer tuple when a template slot calls a plain function")
val pairs = [("count", 1), ("ready", 2)]
val result = pairs.map("{_.0}: {double_val(_.1)}")
expect result == ["count: 2", "ready: 4"]
```

</details>

#### keeps `_` bound to the outer tuple when a template slot calls a method (type_mapper map_struct shape)

- keeps `_` bound to the outer tuple when a template slot calls a method (type_mapper map_struct shape)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps `_` bound to the outer tuple when a template slot calls a method (type_mapper map_struct shape)")
val pairs = [("count", 1), ("ready", 2)]
val doubler = Doubler.create()
val result = pairs.map("{_.0}: {doubler.apply(_.1)}")
expect result == ["count: 2", "ready: 4"]
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

- Canonical SPipe generation for source `a7b0b262fa3f43d9113b375cf7904d737a83a0babb75ee94ec753bf74e15769e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7b0b262fa3f43d9113b375cf7904d737a83a0babb75ee94ec753bf74e15769e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7b0b262fa3f43d9113b375cf7904d737a83a0babb75ee94ec753bf74e15769e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/placeholder_lambda_spec.spl
mirror: doc/06_spec/03_system/feature/usage/placeholder_lambda_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/placeholder_lambda_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/placeholder_lambda_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/placeholder_lambda_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters with less than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/placeholder_lambda_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters with greater than' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/placeholder_lambda_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters with less than or equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
