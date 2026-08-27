# Basic Expressions (Python-Inspired Sample)

> Tests compilation of basic expression patterns inspired by Python syntax including arithmetic, string operations, and comparisons. Verifies that Python-like expression idioms compile correctly through the native compilation pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Expressions (Python-Inspired Sample)

Tests compilation of basic expression patterns inspired by Python syntax including arithmetic, string operations, and comparisons. Verifies that Python-like expression idioms compile correctly through the native compilation pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of basic expression patterns inspired by Python syntax including
arithmetic, string operations, and comparisons. Verifies that Python-like expression
idioms compile correctly through the native compilation pipeline.

## Scenarios

### Basic Expressions

#### arithmetic expressions

#### evaluates addition

- evaluates addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates addition")
expect 2 + 3 == 5
```

</details>

#### evaluates subtraction

- evaluates subtraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates subtraction")
expect 10 - 4 == 6
```

</details>

#### evaluates multiplication

- evaluates multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates multiplication")
expect 3 * 4 == 12
```

</details>

#### evaluates division

- evaluates division


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates division")
expect 10 / 2 == 5
```

</details>

#### evaluates modulo

- evaluates modulo


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates modulo")
expect 10 % 3 == 1
```

</details>

#### comparison operators

#### compares with less than

- compares with less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares with less than")
expect 3 < 5
```

</details>

#### compares with greater than

- compares with greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares with greater than")
expect 7 > 4
```

</details>

#### compares equality

- compares equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares equality")
expect 5 == 5
```

</details>

#### compares inequality

- compares inequality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares inequality")
expect 3 != 4
```

</details>

#### boolean expressions

#### evaluates logical and

- evaluates logical and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates logical and")
expect true && true == true
expect true && false == false
```

</details>

#### evaluates logical or

- evaluates logical or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates logical or")
expect false || true == true
expect false || false == false
```

</details>

#### evaluates logical not

- evaluates logical not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates logical not")
expect not false == true
expect not true == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `a29764468f00b828722a7f987903b3a54683baf62438fd9dbf58fff1261fbc35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a29764468f00b828722a7f987903b3a54683baf62438fd9dbf58fff1261fbc35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a29764468f00b828722a7f987903b3a54683baf62438fd9dbf58fff1261fbc35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/basic_expressions_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
