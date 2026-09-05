# Math Utils Specification

> Tests covering Math Utilities, Absolute Value, Min/Max, Clamp, Sign, Power, GCD and LCM, Factorial and Binomial, Even/Odd, Divisibility, Range, Statistics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Utils Specification

## Scenarios

### Math Utilities

### Absolute Value

#### returns positive for positive

- returns positive for positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns positive for positive")
expect abs_i64(5) == 5
```

</details>

#### returns positive for negative

- returns positive for negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns positive for negative")
expect abs_i64(-5) == 5
```

</details>

#### returns zero for zero

- returns zero for zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero for zero")
expect abs_i64(0) == 0
```

</details>

### Min/Max

#### min returns smaller

- min returns smaller


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("min returns smaller")
expect min_i64(a=5, b=10) == 5
expect min_i64(a=-5, b=3) == -5
```

</details>

#### max returns larger

- max returns larger


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("max returns larger")
expect max_i64(a=5, b=10) == 10
expect max_i64(a=-5, b=3) == 3
```

</details>

### Clamp

#### clamps within range

- clamps within range


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps within range")
expect clamp_i64(x=5, min_val=0, max_val=10) == 5
```

</details>

#### clamps below min

- clamps below min


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps below min")
expect clamp_i64(x=-5, min_val=0, max_val=10) == 0
```

</details>

#### clamps above max

- clamps above max


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps above max")
expect clamp_i64(x=15, min_val=0, max_val=10) == 10
```

</details>

### Sign

#### returns 1 for positive

- returns 1 for positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for positive")
expect sign_i64(5) == 1
```

</details>

#### returns -1 for negative

- returns -1 for negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for negative")
expect sign_i64(-5) == -1
```

</details>

#### returns 0 for zero

- returns 0 for zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for zero")
expect sign_i64(0) == 0
```

</details>

### Power

#### calculates powers

- calculates powers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates powers")
expect pow_i64(base=2, exp=3) == 8
expect pow_i64(base=3, exp=2) == 9
```

</details>

#### handles zero exponent

- handles zero exponent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero exponent")
expect pow_i64(base=10, exp=0) == 1
```

</details>

#### handles zero base

- handles zero base


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero base")
expect pow_i64(base=0, exp=5) == 0
```

</details>

#### handles negative base

- handles negative base


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative base")
expect pow_i64(base=-2, exp=3) == -8
expect pow_i64(base=-2, exp=4) == 16
```

</details>

### GCD and LCM

#### calculates gcd

- calculates gcd


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates gcd")
expect gcd(a=12, b=8) == 4
expect gcd(a=21, b=14) == 7
expect gcd(a=17, b=19) == 1
```

</details>

#### gcd with same number

- gcd with same number


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gcd with same number")
expect gcd(a=10, b=10) == 10
```

</details>

#### gcd with zero

- gcd with zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gcd with zero")
expect gcd(a=0, b=5) == 5
expect gcd(a=5, b=0) == 5
```

</details>

#### calculates lcm

- calculates lcm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates lcm")
expect lcm(a=4, b=6) == 12
expect lcm(a=3, b=5) == 15
```

</details>

### Factorial and Binomial

#### calculates factorial

- calculates factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates factorial")
expect factorial(0) == 1
expect factorial(1) == 1
expect factorial(5) == 120
```

</details>

#### calculates binomial

- calculates binomial


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates binomial")
expect binomial(n=5, k=2) == 10
expect binomial(n=4, k=2) == 6
expect binomial(n=5, k=0) == 1
expect binomial(n=5, k=5) == 1
```

</details>

### Even/Odd

#### detects even

- detects even


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects even")
expect is_even(0)
expect is_even(2)
expect is_even(-4)
expect not is_even(1)
```

</details>

#### detects odd

- detects odd


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects odd")
expect is_odd(1)
expect is_odd(3)
expect not is_odd(0)
```

</details>

### Divisibility

#### checks divisibility

- checks divisibility


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks divisibility")
expect is_divisible_by(x=10, d=2)
expect is_divisible_by(x=15, d=5)
expect not is_divisible_by(x=7, d=3)
```

</details>

### Range

#### checks in range

- checks in range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks in range")
expect in_range_i64(x=5, min_val=0, max_val=10)
expect not in_range_i64(x=-1, min_val=0, max_val=10)
expect not in_range_i64(x=11, min_val=0, max_val=10)
```

</details>

### Statistics

#### calculates sum

- calculates sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates sum")
expect sum_i64([1, 2, 3, 4, 5]) == 15
```

</details>

#### sum of empty is 0

- sum of empty is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sum of empty is 0")
val empty_list: [i64] = []
expect sum_i64(empty_list) == 0
```

</details>

#### calculates product

- calculates product


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates product")
expect product_i64([2, 3, 4]) == 24
```

</details>

#### product of empty is 1

- product of empty is 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("product of empty is 1")
val empty_list: [i64] = []
expect product_i64(empty_list) == 1
```

</details>

#### calculates average

- calculates average


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates average")
val result = average_i64([1, 2, 3, 4, 5])
expect result == 3
```

</details>

#### average of empty is nil

- average of empty is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("average of empty is nil")
val empty_list: [i64] = []
val result = average_i64(empty_list)
expect result == nil
```

</details>

#### calculates median odd

- calculates median odd


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates median odd")
val result = median_i64([1, 2, 3, 4, 5])
expect result == 3
```

</details>

#### calculates median even

- calculates median even


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates median even")
val result = median_i64([1, 2, 3, 4])
expect result == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/math_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Math Utilities, Absolute Value, Min/Max, Clamp, Sign, Power, GCD and LCM, Factorial and Binomial, Even/Odd, Divisibility, Range, Statistics.
- Math Utilities
- Absolute Value
- Min/Max
- Clamp
- Sign
- Power
- GCD and LCM
- Factorial and Binomial
- Even/Odd
- Divisibility
- Range
- Statistics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `0c2534766fa2e55f55903ecdfd745d2849e27137e9fb772bc03c5ccd952061a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c2534766fa2e55f55903ecdfd745d2849e27137e9fb772bc03c5ccd952061a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c2534766fa2e55f55903ecdfd745d2849e27137e9fb772bc03c5ccd952061a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/math_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/math_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/math_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/math_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/math_utils_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns positive for positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/math_utils_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns positive for negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/math_utils_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
