# Basic Expressions (Interpreter)

> Tests basic expression evaluation in the interpreter including arithmetic, string operations, and type coercion. Verifies that the interpreter correctly computes expression results matching the compiled output behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Expressions (Interpreter)

Tests basic expression evaluation in the interpreter including arithmetic, string operations, and type coercion. Verifies that the interpreter correctly computes expression results matching the compiled output behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests basic expression evaluation in the interpreter including arithmetic, string
operations, and type coercion. Verifies that the interpreter correctly computes
expression results matching the compiled output behavior.

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
expect 6 * 7 == 42
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
expect 20 / 4 == 5
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
expect 17 % 5 == 2
```

</details>

#### respects operator precedence

- respects operator precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("respects operator precedence")
expect 2 + 3 * 4 == 14
```

</details>

#### comparison expressions

#### compares equality

- compares equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares equality")
expect (5 == 5) == true
expect (5 == 6) == false
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
expect (5 != 6) == true
```

</details>

#### compares less than

- compares less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares less than")
expect (3 < 5) == true
expect (5 < 3) == false
```

</details>

#### compares greater than

- compares greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares greater than")
expect (5 > 3) == true
```

</details>

#### logical expressions

#### evaluates and

- evaluates and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates and")
expect (true && true) == true
expect (true && false) == false
```

</details>

#### evaluates or

- evaluates or


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates or")
expect (false || true) == true
expect (false || false) == false
```

</details>

#### evaluates not

- evaluates not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates not")
expect (not true) == false
expect (not false) == true
```

</details>

#### string expressions

#### concatenates strings

- concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("concatenates strings")
val result = "hello" + " " + "world"
expect result == "hello world"
```

</details>

#### interpolates values

- interpolates values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpolates values")
val x = 42
val msg = "value is {x}"
expect msg == "value is 42"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `bbe55f7c0ff5032f92549e6c6707b413687257a9a8323a49cd90ce1cc67bd884`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbe55f7c0ff5032f92549e6c6707b413687257a9a8323a49cd90ce1cc67bd884`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbe55f7c0ff5032f92549e6c6707b413687257a9a8323a49cd90ce1cc67bd884`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl
mirror: doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates subtraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/interpreter/sample/python_inspired_sample/basic_expressions_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
