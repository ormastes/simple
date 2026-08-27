# UFCS (Uniform Function Call Syntax) Specification

> UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the compiler resolves in priority order: 1. Instance method on x's type (highest priority) 2. Trait method implemented by x's type 3. Free function `method(x)` where first param matches x's type (UFCS)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UFCS (Uniform Function Call Syntax) Specification

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax. When `x.method()` is called, the compiler resolves in priority order: 1. Instance method on x's type (highest priority) 2. Trait method implemented by x's type 3. Free function `method(x)` where first param matches x's type (UFCS)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3100-3120 |
| Category | Syntax |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/ufcs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax.
When `x.method()` is called, the compiler resolves in priority order:
1. Instance method on x's type (highest priority)
2. Trait method implemented by x's type
3. Free function `method(x)` where first param matches x's type (UFCS)

This enables fluent API chaining without requiring methods to be defined on types.

## Syntax

```simple
# Free function
use std.spec.step

fn double(x: i64) -> i64:
x * 2

# Usage via UFCS
val n = 5
val result = n.double()    # Resolves to: double(n)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| UFCS | Uniform Function Call Syntax - call free functions as methods |
| Resolution Priority | Instance > Trait > FreeFunction |
| Type Matching | First parameter type must be compatible with receiver |

## Implementation Notes

Files involved:
- `simple/compiler/hir.spl` - MethodResolution enum
- `simple/compiler/resolve.spl` - Resolution pass
- `simple/compiler/mir.spl` - Codegen support
- `simple/compiler/driver.spl` - Pipeline integration

## Scenarios

### UFCS Basic Functionality

#### with integer values

#### calls math.abs via dot notation

- calls math.abs via dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls math.abs via dot notation")
val n = -5
val result = n.abs()
expect result == 5
```

</details>

#### calls math.sqrt via dot notation

- calls math.sqrt via dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls math.sqrt via dot notation")
val x = 16.0
val result = x.sqrt()
expect result == 4.0
```

</details>

#### with array values

#### calls array.len via dot notation

- calls array.len via dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls array.len via dot notation")
var arr = [1, 2, 3, 4, 5]
val result = arr.len()
expect result == 5
```

</details>

#### calls array.first via dot notation

- calls array.first via dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls array.first via dot notation")
var arr = [10, 20, 30]
val result = arr.first()
expect result == 10
```

</details>

#### calls array.last via dot notation

- calls array.last via dot notation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls array.last via dot notation")
var arr = [10, 20, 30]
val result = arr.last()
expect result == 30
```

</details>

### UFCS Method Chaining

#### chaining multiple UFCS calls

#### chains abs and to_string

- chains abs and to_string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains abs and to_string")
val n = -42
val result = n.abs().to_string()
expect result == "42"
```

</details>

#### chains array operations

- chains array operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains array operations")
var arr = [1, 2, 3]
val result = arr.len().to_string()
expect result == "3"
```

</details>

### UFCS Priority Ordering

#### instance method takes priority

#### calls string.len method not free function

- calls string.len method not free function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls string.len method not free function")
val s = "hello"
val result = s.len()
expect result == 5
```

</details>

#### calls array.push method

- calls array.push method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls array.push method")
var arr = [1, 2, 3]
arr = arr.push(4)
expect arr.len() == 4
```

</details>

### UFCS Type Matching

#### exact type matching

#### matches i64 receiver with i64 parameter

- matches i64 receiver with i64 parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches i64 receiver with i64 parameter")
val n: i64 = -5
val result = n.abs()
expect result == 5
```

</details>

#### matches f64 receiver with f64 parameter

- matches f64 receiver with f64 parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches f64 receiver with f64 parameter")
val x: f64 = 16.0
val result = x.sqrt()
expect result == 4.0
```

</details>

### UFCS Edge Cases

#### with zero and negative values

#### works with zero

- works with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with zero")
val n = 0
val result = n.abs()
expect result == 0
```

</details>

#### works with negative float

- works with negative float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with negative float")
val x = -3.14
val result = x.abs()
expect result == 3.14
```

</details>

#### with empty collections

#### len of empty array is zero

- len of empty array is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("len of empty array is zero")
val arr: [i64] = []
val result = arr.len()
expect result == 0
```

</details>

#### first of empty array is None

- first of empty array is None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("first of empty array is None")
val arr: [i64] = []
val result = arr.first()
expect result == nil
```

</details>

#### receiver as expression

#### works with literal receiver

- works with literal receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with literal receiver")
val result = (-5).abs()
expect result == 5
```

</details>

#### works with arithmetic expression receiver

- works with arithmetic expression receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with arithmetic expression receiver")
val result = (3 - 8).abs()
expect result == 5
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `21e8a8b1309e371824cd6dff69961c13d8912e7075eb68abe1ba61113753a1e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21e8a8b1309e371824cd6dff69961c13d8912e7075eb68abe1ba61113753a1e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21e8a8b1309e371824cd6dff69961c13d8912e7075eb68abe1ba61113753a1e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/ufcs_spec.spl
mirror: doc/06_spec/feature/usage/ufcs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/ufcs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/ufcs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/ufcs_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls math.abs via dot notation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/ufcs_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls math.sqrt via dot notation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/ufcs_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls array.len via dot notation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
