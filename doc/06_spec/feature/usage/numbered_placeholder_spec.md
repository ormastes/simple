# Numbered Placeholder Lambda Expressions

> Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand. Covers basic single-parameter usage with map and filter, method calls on numbered placeholders, compound arithmetic expressions, edge cases (empty collections, single elements), and chaining filter/map operations with numbered placeholders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numbered Placeholder Lambda Expressions

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand. Covers basic single-parameter usage with map and filter, method calls on numbered placeholders, compound arithmetic expressions, edge cases (empty collections, single elements), and chaining filter/map operations with numbered placeholders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/numbered_placeholder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit
parameter ordering in lambda shorthand. Covers basic single-parameter usage with map
and filter, method calls on numbered placeholders, compound arithmetic expressions,
edge cases (empty collections, single elements), and chaining filter/map operations
with numbered placeholders.

## Scenarios

### Numbered Placeholder Lambda

#### basic numbered placeholders

#### uses _1 as single param

- uses _1 as single param
   - Expected: result equals `[10, 20, 30]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 as single param")
val data = [1, 2, 3]
val result = data.map(_1 * 10)
expect(result).to_equal([10, 20, 30])
```

</details>

#### uses _1 in filter

- uses _1 in filter
   - Expected: result equals `[4, 5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 in filter")
val data = [1, 2, 3, 4, 5]
val result = data.filter(_1 > 3)
expect(result).to_equal([4, 5])
```

</details>

#### uses _1 with addition

- uses _1 with addition
   - Expected: result equals `[15, 25, 35]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 with addition")
val data = [10, 20, 30]
val result = data.map(_1 + 5)
expect(result).to_equal([15, 25, 35])
```

</details>

#### two numbered params

#### uses _1 and _2 in order

- uses _1 and _2 in order
   - Expected: result equals `[20, 40, 60]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 and _2 in order")
val nums = [10, 20, 30]
val result = nums.map(_1 * 2)
expect(result).to_equal([20, 40, 60])
```

</details>

#### numbered with method calls

#### calls method on _1

- calls method on _1
   - Expected: result equals `["hello", "hey"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls method on _1")
val words = ["hi", "hello", "hey"]
val result = words.filter(_1.len() > 2)
expect(result).to_equal(["hello", "hey"])
```

</details>

#### numbered in compound expressions

#### uses _1 in modulo

- uses _1 in modulo
   - Expected: result equals `[2, 4, 6]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 in modulo")
val data = [1, 2, 3, 4, 5, 6]
val result = data.filter(_1 % 2 == 0)
expect(result).to_equal([2, 4, 6])
```

</details>

#### uses _1 in compound arithmetic

- uses _1 in compound arithmetic
   - Expected: result equals `[4, 7, 10]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses _1 in compound arithmetic")
val data = [1, 2, 3]
val result = data.map(_1 * 3 + 1)
expect(result).to_equal([4, 7, 10])
```

</details>

#### edge cases

#### numbered on empty collection

- numbered on empty collection
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("numbered on empty collection")
val data: [i64] = []
val result = data.filter(_1 > 0)
expect(result).to_equal([])
```

</details>

#### numbered on single element

- numbered on single element
   - Expected: result equals `[50]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("numbered on single element")
val data = [42]
val result = data.map(_1 + 8)
expect(result).to_equal([50])
```

</details>

#### numbered with collection methods

#### works with any

- works with any
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with any")
val data = [1, 2, 3]
val result = data.any(_1 > 2)
expect(result).to_equal(true)
```

</details>

#### works with all

- works with all
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with all")
val data = [2, 4, 6]
val result = data.all(_1 % 2 == 0)
expect(result).to_equal(true)
```

</details>

#### chaining numbered placeholders

#### chains filter then map with numbered

- chains filter then map with numbered
   - Expected: result equals `[6, 8, 10]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains filter then map with numbered")
val data = [1, 2, 3, 4, 5]
val filtered = data.filter(_1 > 2)
val result = filtered.map(_1 * 2)
expect(result).to_equal([6, 8, 10])
```

</details>

#### chains map then filter with numbered

- chains map then filter with numbered
   - Expected: result equals `[6, 8, 10]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains map then filter with numbered")
val data = [1, 2, 3, 4, 5]
val mapped = data.map(_1 * 2)
val result = mapped.filter(_1 > 5)
expect(result).to_equal([6, 8, 10])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `7c3453bce0887d89f581beb24350e49d06d897a7e3219d7790a37d053a6eea3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c3453bce0887d89f581beb24350e49d06d897a7e3219d7790a37d053a6eea3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c3453bce0887d89f581beb24350e49d06d897a7e3219d7790a37d053a6eea3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/numbered_placeholder_spec.spl
mirror: doc/06_spec/feature/usage/numbered_placeholder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/numbered_placeholder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/numbered_placeholder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/numbered_placeholder_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses _1 as single param' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/numbered_placeholder_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses _1 in filter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/numbered_placeholder_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses _1 with addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
