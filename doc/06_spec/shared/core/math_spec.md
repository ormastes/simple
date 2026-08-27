# Math Specification

> Tests covering Math operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Specification

## Scenarios

### Math operations

#### Basic operations

#### abs returns absolute value of negative

- abs returns absolute value of negative
   - Expected: abs_val(-5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("abs returns absolute value of negative")
expect(abs_val(-5)).to_equal(5)
```

</details>

#### abs of positive is unchanged

- abs of positive is unchanged
   - Expected: abs_val(5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("abs of positive is unchanged")
expect(abs_val(5)).to_equal(5)
```

</details>

#### abs of zero is zero

- abs of zero is zero
   - Expected: abs_val(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("abs of zero is zero")
expect(abs_val(0)).to_equal(0)
```

</details>

#### sign returns -1 for negative

- sign returns -1 for negative
   - Expected: sign_val(-5) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("sign returns -1 for negative")
expect(sign_val(-5)).to_equal(-1)
```

</details>

#### sign returns 1 for positive

- sign returns 1 for positive
   - Expected: sign_val(5) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("sign returns 1 for positive")
expect(sign_val(5)).to_equal(1)
```

</details>

#### sign returns 0 for zero

- sign returns 0 for zero
   - Expected: sign_val(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("sign returns 0 for zero")
expect(sign_val(0)).to_equal(0)
```

</details>

#### Min/Max functions

#### min returns smaller value

- min returns smaller value
   - Expected: min_val(3, 5) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("min returns smaller value")
expect(min_val(3, 5)).to_equal(3)
```

</details>

#### min with equal values

- min with equal values
   - Expected: min_val(4, 4) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("min with equal values")
expect(min_val(4, 4)).to_equal(4)
```

</details>

#### min with negative

- min with negative
   - Expected: min_val(-3, 5) equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("min with negative")
expect(min_val(-3, 5)).to_equal(-3)
```

</details>

#### max returns larger value

- max returns larger value
   - Expected: max_val(3, 5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("max returns larger value")
expect(max_val(3, 5)).to_equal(5)
```

</details>

#### max with equal values

- max with equal values
   - Expected: max_val(4, 4) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("max with equal values")
expect(max_val(4, 4)).to_equal(4)
```

</details>

#### max with negative

- max with negative
   - Expected: max_val(-3, 5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("max with negative")
expect(max_val(-3, 5)).to_equal(5)
```

</details>

#### Clamping

#### clamp within range returns value

- clamp within range returns value
   - Expected: clamp_val(5, 0, 10) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("clamp within range returns value")
expect(clamp_val(5, 0, 10)).to_equal(5)
```

</details>

#### clamp below range returns min

- clamp below range returns min
   - Expected: clamp_val(-5, 0, 10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("clamp below range returns min")
expect(clamp_val(-5, 0, 10)).to_equal(0)
```

</details>

#### clamp above range returns max

- clamp above range returns max
   - Expected: clamp_val(15, 0, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("clamp above range returns max")
expect(clamp_val(15, 0, 10)).to_equal(10)
```

</details>

#### clamp at boundaries

- clamp at boundaries
   - Expected: clamp_val(0, 0, 10) equals `0`
   - Expected: clamp_val(10, 0, 10) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("clamp at boundaries")
expect(clamp_val(0, 0, 10)).to_equal(0)
expect(clamp_val(10, 0, 10)).to_equal(10)
```

</details>

#### Integer math

#### factorial computes 5!

- factorial computes 5!
   - Expected: factorial(5) equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("factorial computes 5!")
expect(factorial(5)).to_equal(120)
```

</details>

#### factorial of 0 is 1

- factorial of 0 is 1
   - Expected: factorial(0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("factorial of 0 is 1")
expect(factorial(0)).to_equal(1)
```

</details>

#### factorial of 1 is 1

- factorial of 1 is 1
   - Expected: factorial(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("factorial of 1 is 1")
expect(factorial(1)).to_equal(1)
```

</details>

#### factorial of 10

- factorial of 10
   - Expected: factorial(10) equals `3628800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("factorial of 10")
expect(factorial(10)).to_equal(3628800)
```

</details>

#### gcd computes greatest common divisor

- gcd computes greatest common divisor
   - Expected: gcd(12, 8) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("gcd computes greatest common divisor")
expect(gcd(12, 8)).to_equal(4)
```

</details>

#### gcd of coprime numbers is 1

- gcd of coprime numbers is 1
   - Expected: gcd(7, 13) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("gcd of coprime numbers is 1")
expect(gcd(7, 13)).to_equal(1)
```

</details>

#### gcd with zero

- gcd with zero
   - Expected: gcd(5, 0) equals `5`
   - Expected: gcd(0, 5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("gcd with zero")
expect(gcd(5, 0)).to_equal(5)
expect(gcd(0, 5)).to_equal(5)
```

</details>

#### lcm computes least common multiple

- lcm computes least common multiple
   - Expected: lcm(4, 6) equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("lcm computes least common multiple")
expect(lcm(4, 6)).to_equal(12)
```

</details>

#### lcm of coprime numbers

- lcm of coprime numbers
   - Expected: lcm(3, 5) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("lcm of coprime numbers")
expect(lcm(3, 5)).to_equal(15)
```

</details>

#### lcm with zero

- lcm with zero
   - Expected: lcm(0, 5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("lcm with zero")
expect(lcm(0, 5)).to_equal(0)
```

</details>

#### Arithmetic properties

#### addition is commutative

- addition is commutative
   - Expected: 3 + 5 equals `5 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("addition is commutative")
expect(3 + 5).to_equal(5 + 3)
```

</details>

#### multiplication is commutative

- multiplication is commutative
   - Expected: 3 * 5 equals `5 * 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiplication is commutative")
expect(3 * 5).to_equal(5 * 3)
```

</details>

#### multiplication distributes over addition

- multiplication distributes over addition
   - Expected: 3 * (4 + 5) equals `3 * 4 + 3 * 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("multiplication distributes over addition")
expect(3 * (4 + 5)).to_equal(3 * 4 + 3 * 5)
```

</details>

#### integer division truncates toward zero

- integer division truncates toward zero
   - Expected: 7 / 2 equals `3`
   - Expected: -7 / 2 equals `-3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("integer division truncates toward zero")
expect(7 / 2).to_equal(3)
expect(-7 / 2).to_equal(-3)
```

</details>

#### modulo gives remainder

- modulo gives remainder
   - Expected: 7 % 3 equals `1`
   - Expected: 10 % 5 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("modulo gives remainder")
expect(7 % 3).to_equal(1)
expect(10 % 5).to_equal(0)
```

</details>

#### Power via repeated multiplication

#### computes x^0 = 1

- computes x^0 = 1
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("computes x^0 = 1")
val base = 5
expect(1).to_equal(1)
```

</details>

#### computes 2^10 = 1024

- computes 2^10 = 1024
   - Expected: result equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("computes 2^10 = 1024")
var result = 1
for _ in 0..10:
    result = result * 2
expect(result).to_equal(1024)
```

</details>

#### computes 3^5 = 243

- computes 3^5 = 243
   - Expected: result equals `243`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("computes 3^5 = 243")
var result = 1
for _ in 0..5:
    result = result * 3
expect(result).to_equal(243)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/core/math_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math operations.
- Math operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
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

- Canonical SPipe generation for source `2b3ff6e4f9bb2a1ab8340cc96502479fbfbf9dc97d25a3cc25bec5a4669bf8f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b3ff6e4f9bb2a1ab8340cc96502479fbfbf9dc97d25a3cc25bec5a4669bf8f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b3ff6e4f9bb2a1ab8340cc96502479fbfbf9dc97d25a3cc25bec5a4669bf8f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/shared/core/math_spec.spl
mirror: doc/06_spec/shared/core/math_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/core/math_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/core/math_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/core/math_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 35 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/shared/core/math_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'abs returns absolute value of negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/math_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'abs of positive is unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/core/math_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'abs of zero is zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
