# Simple Language Metaprogramming - Test Specification

> This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Metaprogramming - Test Specification

This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtime.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Various |
| Category | Language Features |
| Status | Partial Implementation |
| Type | Extracted Examples |
| Reference | metaprogramming.md |
| Source | `test/feature/usage/metaprogramming_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases for metaprogramming features that are
currently implemented in Simple's runtime.

Tests cover: comprehensions, indexing, pattern matching, and basic error handling.

**Note:** Advanced features (DSL blocks, decorators, slicing, context managers, move closures)
are not yet fully implemented.

## Scenarios

### Metaprogramming Spec

#### list comprehensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- list comprehensions
- list comprehensions
   - Expected: evens[0] equals `0`
   - Expected: evens[1] equals `2`
   - Expected: evens[2] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("list comprehensions")
step("list comprehensions")
# @req: REQ-FEAT-USAGE-METAPROGRAMMING-SPEC-001
# List comprehensions with filters
val evens = [for x in 0..10 if x % 2 == 0: x]
expect(evens[0]).to_equal(0)
expect(evens[1]).to_equal(2)
expect(evens[2]).to_equal(4)
```

</details>

#### list comprehensions - transformation

- list comprehensions - transformation
- list comprehensions - transformation
   - Expected: squares[0] equals `1`
   - Expected: squares[1] equals `4`
   - Expected: squares[2] equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("list comprehensions - transformation")
step("list comprehensions - transformation")
# Transform elements in comprehension
val squares = [for x in 1..6: x * x]
expect(squares[0]).to_equal(1)
expect(squares[1]).to_equal(4)
expect(squares[2]).to_equal(9)
```

</details>

#### array indexing - basic

- array indexing - basic
- array indexing - basic
   - Expected: arr[0] equals `10`
   - Expected: arr[2] equals `30`
   - Expected: arr[4] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("array indexing - basic")
step("array indexing - basic")
# Basic array indexing
val arr = [10, 20, 30, 40, 50]
expect(arr[0]).to_equal(10)
expect(arr[2]).to_equal(30)
expect(arr[4]).to_equal(50)
```

</details>

#### array indexing - last element

- array indexing - last element
- array indexing - last element
   - Expected: last equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("array indexing - last element")
step("array indexing - last element")
# Access last element using len()
val arr = [10, 20, 30, 40, 50]
val last = arr[arr.len() - 1]
expect(last).to_equal(50)
```

</details>

#### pattern matching - guard patterns

- pattern matching - guard patterns
- pattern matching - guard patterns
   - Expected: classify(-5) equals `negative`
   - Expected: classify(0) equals `zero`
   - Expected: classify(10) equals `positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pattern matching - guard patterns")
step("pattern matching - guard patterns")
# Guard patterns using if/else
fn classify(n: i64) -> text:
    if n < 0:
        return "negative"
    else if n == 0:
        return "zero"
    else:
        return "positive"

expect(classify(-5)).to_equal("negative")
expect(classify(0)).to_equal("zero")
expect(classify(10)).to_equal("positive")
```

</details>

#### pattern matching - simple matching

- pattern matching - simple matching
- pattern matching - simple matching
   - Expected: find_value(numbers, 20) equals `found`
   - Expected: find_value(numbers, 99) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pattern matching - simple matching")
step("pattern matching - simple matching")
# Simple value matching with functions
fn find_value(arr: [i64], target: i64) -> text:
    for x in arr:
        if x == target:
            return "found"
    return "not found"

val numbers = [10, 20, 30]
expect(find_value(numbers, 20)).to_equal("found")
expect(find_value(numbers, 99)).to_equal("not found")
```

</details>

#### error handling - safe division

- error handling - safe division
- error handling - safe division
   - Expected: result1 equals `5`
   - Expected: result2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("error handling - safe division")
step("error handling - safe division")
# Safe operations with error returns
fn safe_divide(a: i64, b: i64) -> i64:
    if b == 0:
        return 0  # Error sentinel
    a / b

val result1 = safe_divide(10, 2)
val result2 = safe_divide(10, 0)

expect(result1).to_equal(5)
expect(result2).to_equal(0)
```

</details>

#### error handling - option pattern

- error handling - option pattern
- error handling - option pattern
   - Expected: result equals `6`
   - Expected: not_found equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("error handling - option pattern")
step("error handling - option pattern")
# Option pattern with nil checking
fn find_first_even(arr: [i64]) -> i64:
    for x in arr:
        if x % 2 == 0:
            return x
    return -1  # Not found sentinel

val numbers = [1, 3, 6, 9]
val result = find_first_even(numbers)
expect(result).to_equal(6)

val odd_only = [1, 3, 5]
val not_found = find_first_even(odd_only)
expect(not_found).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-METAPROGRAMMING-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a1aa95b742c41e8595fa78dfe6b3067b76e4184b08c4482c47fda00fec3d0823`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1aa95b742c41e8595fa78dfe6b3067b76e4184b08c4482c47fda00fec3d0823`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1aa95b742c41e8595fa78dfe6b3067b76e4184b08c4482c47fda00fec3d0823`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/metaprogramming_spec.spl
mirror: doc/06_spec/feature/usage/metaprogramming_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/metaprogramming_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/metaprogramming_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/metaprogramming_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/metaprogramming_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'list comprehensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/metaprogramming_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'list comprehensions - transformation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/metaprogramming_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'array indexing - basic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
