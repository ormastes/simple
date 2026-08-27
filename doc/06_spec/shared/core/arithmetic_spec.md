# Arithmetic Specification

> Tests covering Arithmetic, addition, subtraction, multiplication, division, precedence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arithmetic Specification

## Scenarios

### Arithmetic

### addition

#### adds two numbers

- adds two numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("adds two numbers")
expect 1 + 1 == 2
```

</details>

#### adds multiple numbers

- adds multiple numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("adds multiple numbers")
expect 1 + 2 + 3 == 6
```

</details>

### subtraction

#### subtracts two numbers

- subtracts two numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("subtracts two numbers")
expect 5 - 3 == 2
```

</details>

#### subtracts to zero

- subtracts to zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("subtracts to zero")
expect 5 - 5 == 0
```

</details>

### multiplication

#### multiplies two numbers

- multiplies two numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiplies two numbers")
expect 3 * 4 == 12
```

</details>

#### multiplies by zero

- multiplies by zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiplies by zero")
expect 5 * 0 == 0
```

</details>

### division

#### divides evenly

- divides evenly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("divides evenly")
expect 10 / 2 == 5
```

</details>

#### integer division

- integer division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("integer division")
expect 7 / 2 == 3
```

</details>

### precedence

#### multiplication before addition

- multiplication before addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiplication before addition")
expect 2 + 3 * 4 == 14
```

</details>

#### parentheses override precedence

- parentheses override precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("parentheses override precedence")
expect (2 + 3) * 4 == 20
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/core/arithmetic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Arithmetic, addition, subtraction, multiplication, division, precedence.
- Arithmetic
- addition
- subtraction
- multiplication
- division
- precedence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e2cef2be1764ad6dde11df1b5fa92abdd86a13016d1ed2100cbab29e0b5be05b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2cef2be1764ad6dde11df1b5fa92abdd86a13016d1ed2100cbab29e0b5be05b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2cef2be1764ad6dde11df1b5fa92abdd86a13016d1ed2100cbab29e0b5be05b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/core/arithmetic_spec.spl
mirror: doc/06_spec/shared/core/arithmetic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/core/arithmetic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/core/arithmetic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/core/arithmetic_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds two numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/arithmetic_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds multiple numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/arithmetic_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'subtracts two numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
