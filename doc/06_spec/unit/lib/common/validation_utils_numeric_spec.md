# Validation Utils Numeric Specification

> Tests covering std.validation_utils, is_positive, is_negative, is_non_negative, is_zero, is_in_range, is_outside_range, is_not_empty, is_empty, is_divisible, is_multiple_of.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Utils Numeric Specification

## Scenarios

### std.validation_utils

### is_positive

#### returns true for positive numbers

- returns true for positive numbers
   - Expected: is_positive(1) is true
   - Expected: is_positive(42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for positive numbers")
expect(is_positive(1)).to_equal(true)
expect(is_positive(42)).to_equal(true)
```

</details>

#### returns false for zero and negatives

- returns false for zero and negatives
   - Expected: is_positive(0) is false
   - Expected: is_positive(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for zero and negatives")
expect(is_positive(0)).to_equal(false)
expect(is_positive(-1)).to_equal(false)
```

</details>

### is_negative

#### returns true for negative numbers

- returns true for negative numbers
   - Expected: is_negative(-1) is true
   - Expected: is_negative(-42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for negative numbers")
expect(is_negative(-1)).to_equal(true)
expect(is_negative(-42)).to_equal(true)
```

</details>

#### returns false for zero and positives

- returns false for zero and positives
   - Expected: is_negative(0) is false
   - Expected: is_negative(1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for zero and positives")
expect(is_negative(0)).to_equal(false)
expect(is_negative(1)).to_equal(false)
```

</details>

### is_non_negative

#### returns true for zero and positives

- returns true for zero and positives
   - Expected: is_non_negative(0) is true
   - Expected: is_non_negative(42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for zero and positives")
expect(is_non_negative(0)).to_equal(true)
expect(is_non_negative(42)).to_equal(true)
```

</details>

#### returns false for negatives

- returns false for negatives
   - Expected: is_non_negative(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for negatives")
expect(is_non_negative(-1)).to_equal(false)
```

</details>

### is_zero

#### returns true for zero

- returns true for zero
   - Expected: is_zero(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for zero")
expect(is_zero(0)).to_equal(true)
```

</details>

#### returns false for non-zero

- returns false for non-zero
   - Expected: is_zero(1) is false
   - Expected: is_zero(-1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-zero")
expect(is_zero(1)).to_equal(false)
expect(is_zero(-1)).to_equal(false)
```

</details>

### is_in_range

#### returns true when in range

- returns true when in range
   - Expected: is_in_range(5, 1, 10) is true
   - Expected: is_in_range(1, 1, 10) is true
   - Expected: is_in_range(10, 1, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when in range")
expect(is_in_range(5, 1, 10)).to_equal(true)
expect(is_in_range(1, 1, 10)).to_equal(true)
expect(is_in_range(10, 1, 10)).to_equal(true)
```

</details>

#### returns false when out of range

- returns false when out of range
   - Expected: is_in_range(0, 1, 10) is false
   - Expected: is_in_range(11, 1, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when out of range")
expect(is_in_range(0, 1, 10)).to_equal(false)
expect(is_in_range(11, 1, 10)).to_equal(false)
```

</details>

### is_outside_range

#### returns true when outside range

- returns true when outside range
   - Expected: is_outside_range(0, 1, 10) is true
   - Expected: is_outside_range(11, 1, 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when outside range")
expect(is_outside_range(0, 1, 10)).to_equal(true)
expect(is_outside_range(11, 1, 10)).to_equal(true)
```

</details>

#### returns false when in range

- returns false when in range
   - Expected: is_outside_range(5, 1, 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when in range")
expect(is_outside_range(5, 1, 10)).to_equal(false)
```

</details>

### is_not_empty

#### returns true for non-empty strings

- returns true for non-empty strings
   - Expected: is_not_empty("hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for non-empty strings")
expect(is_not_empty("hello")).to_equal(true)
```

</details>

#### returns false for empty string

- returns false for empty string
   - Expected: is_not_empty("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty string")
expect(is_not_empty("")).to_equal(false)
```

</details>

### is_empty

#### returns true for empty string

- returns true for empty string
   - Expected: is_empty("") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for empty string")
expect(is_empty("")).to_equal(true)
```

</details>

#### returns false for non-empty

- returns false for non-empty
   - Expected: is_empty("hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-empty")
expect(is_empty("hello")).to_equal(false)
```

</details>

### is_divisible

#### checks divisibility

- checks divisibility
   - Expected: is_divisible(10, 5) is true
   - Expected: is_divisible(10, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks divisibility")
expect(is_divisible(10, 5)).to_equal(true)
expect(is_divisible(10, 3)).to_equal(false)
```

</details>

#### handles zero divisor

- handles zero divisor
   - Expected: is_divisible(10, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero divisor")
expect(is_divisible(10, 0)).to_equal(false)
```

</details>

### is_multiple_of

#### checks if multiple

- checks if multiple
   - Expected: is_multiple_of(15, 5) is true
   - Expected: is_multiple_of(15, 4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if multiple")
expect(is_multiple_of(15, 5)).to_equal(true)
expect(is_multiple_of(15, 4)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/validation_utils_numeric_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.validation_utils, is_positive, is_negative, is_non_negative, is_zero, is_in_range, is_outside_range, is_not_empty, is_empty, is_divisible, is_multiple_of.
- std.validation_utils
- is_positive
- is_negative
- is_non_negative
- is_zero
- is_in_range
- is_outside_range
- is_not_empty
- is_empty
- is_divisible
- is_multiple_of

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `26937518b523eed71ba7fdf92d25301837d471cabbdec45d3e2752216af322a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26937518b523eed71ba7fdf92d25301837d471cabbdec45d3e2752216af322a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26937518b523eed71ba7fdf92d25301837d471cabbdec45d3e2752216af322a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/validation_utils_numeric_spec.spl
mirror: doc/06_spec/unit/lib/common/validation_utils_numeric_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/validation_utils_numeric_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/validation_utils_numeric_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/validation_utils_numeric_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for positive numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/validation_utils_numeric_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for zero and negatives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/validation_utils_numeric_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true for negative numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
