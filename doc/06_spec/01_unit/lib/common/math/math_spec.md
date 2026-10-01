# Math Specification

> Tests covering std.math.math (transcendental SFFI wrappers).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Specification

## Scenarios

### std.math.math (transcendental SFFI wrappers)

#### math_sqrt

#### sqrt of 4 is 2

- sqrt of 4 is 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt of 4 is 2")
val res = math_sqrt(4.0)
expect res == 2.0
```

</details>

#### sqrt of 1 is 1

- sqrt of 1 is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt of 1 is 1")
val res = math_sqrt(1.0)
expect res == 1.0
```

</details>

#### sqrt of 0 is 0

- sqrt of 0 is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sqrt of 0 is 0")
val res = math_sqrt(0.0)
expect res == 0.0
```

</details>

#### math_pow

#### 2 raised to 3 is 8

- 2 raised to 3 is 8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2 raised to 3 is 8")
val res = math_pow(2.0, 3.0)
expect res == 8.0
```

</details>

#### anything to power 0 is 1

- anything to power 0 is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("anything to power 0 is 1")
val res = math_pow(5.0, 0.0)
expect res == 1.0
```

</details>

#### math_abs

#### abs of negative is positive

- abs of negative is positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of negative is positive")
val res = math_abs(-3.5)
expect res == 3.5
```

</details>

#### abs of positive is unchanged

- abs of positive is unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of positive is unchanged")
val res = math_abs(3.5)
expect res == 3.5
```

</details>

#### abs of zero is zero

- abs of zero is zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("abs of zero is zero")
val res = math_abs(0.0)
expect res == 0.0
```

</details>

#### math_trunc

#### truncates positive

- truncates positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates positive")
val res = math_trunc(3.9)
expect res == 3.0
```

</details>

#### truncates negative toward zero

- truncates negative toward zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates negative toward zero")
val res = math_trunc(-3.9)
expect res == -3.0
```

</details>

#### math_round

#### rounds half up

- rounds half up


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds half up")
val res = math_round(2.5)
expect res == 3.0
```

</details>

#### rounds down when below half

- rounds down when below half


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds down when below half")
val res = math_round(2.4)
expect res == 2.0
```

</details>

#### rounds negative half away from zero

- rounds negative half away from zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rounds negative half away from zero")
val res = math_round(-2.5)
expect res == -3.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/math_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.math.math (transcendental SFFI wrappers).
- std.math.math (transcendental SFFI wrappers)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9fe422b29b5623e1ed51b4ad4c71469bb549f5a42b5b36006b9cc9d29f012ddb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fe422b29b5623e1ed51b4ad4c71469bb549f5a42b5b36006b9cc9d29f012ddb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fe422b29b5623e1ed51b4ad4c71469bb549f5a42b5b36006b9cc9d29f012ddb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/math/math_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/math_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math/math_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/math_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/math_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sqrt of 4 is 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/math_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sqrt of 1 is 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/math/math_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sqrt of 0 is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
