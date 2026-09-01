# Units Specification

> Tests covering Size Units, Time Units, Combined Unit Operations, Edge Cases and Boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Units Specification

## Scenarios

### Size Units

#### byte count creation

#### creates ByteCount from integer

- creates ByteCount from integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ByteCount from integer")
val b = 1024
expect b == 1024
```

</details>

#### ByteCount zero value

- ByteCount zero value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByteCount zero value")
val zero = 0
expect zero == 0
```

</details>

#### ByteCount comparisons

- ByteCount comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByteCount comparisons")
expect 1024 > 512
expect 512 < 1024
expect 1024 == 1024
```

</details>

#### binary unit conversions

#### converts bytes to kibibytes

- converts bytes to kibibytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to kibibytes")
val bytes = 1024
expect bytes > 0
```

</details>

#### converts bytes to mebibytes

- converts bytes to mebibytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to mebibytes")
val bytes = 1048576
expect bytes > 1024
```

</details>

#### converts bytes to gibibytes

- converts bytes to gibibytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to gibibytes")
val bytes = 1073741824
expect bytes > 1048576
```

</details>

#### ByteCount arithmetic

- ByteCount arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByteCount arithmetic")
val a = 1024
val b = 512
expect (a + b) == 1536
expect (a - b) == 512
```

</details>

#### decimal unit conversions

#### converts bytes to kilobytes

- converts bytes to kilobytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to kilobytes")
val bytes = 1000
expect bytes > 0
```

</details>

#### converts bytes to megabytes

- converts bytes to megabytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to megabytes")
val bytes = 1000000
expect bytes > 1000
```

</details>

#### converts bytes to gigabytes

- converts bytes to gigabytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts bytes to gigabytes")
val bytes = 1000000000
expect bytes > 1000000
```

</details>

#### unit comparisons

#### compares different sizes

- compares different sizes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares different sizes")
val small = 100
val large = 1000
expect large > small
```

</details>

#### size arithmetic operations

- size arithmetic operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size arithmetic operations")
val a = 500
val b = 200
expect (a + b) == 700
expect (a - b) == 300
```

</details>

#### size constants

#### uses kibi constant

- uses kibi constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses kibi constant")
# 1 KiB = 1024 bytes
expect 1024 > 0
```

</details>

#### uses mebi constant

- uses mebi constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses mebi constant")
# 1 MiB = 1048576 bytes
expect 1048576 > 1024
```

</details>

#### uses gibi constant

- uses gibi constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses gibi constant")
# 1 GiB
expect 1073741824 > 1048576
```

</details>

### Time Units

#### nanoseconds

#### creates nanosecond duration

- creates nanosecond duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nanosecond duration")
val ns = 1000
expect ns == 1000
```

</details>

#### zero duration

- zero duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero duration")
val zero = 0
expect zero == 0
```

</details>

#### time unit conversions

#### converts nanoseconds to microseconds

- converts nanoseconds to microseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nanoseconds to microseconds")
val ns = 1000
expect ns > 0
```

</details>

#### converts nanoseconds to milliseconds

- converts nanoseconds to milliseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nanoseconds to milliseconds")
val ns = 1000000
expect ns > 1000
```

</details>

#### converts nanoseconds to seconds

- converts nanoseconds to seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts nanoseconds to seconds")
val ns = 1000000000
expect ns > 1000000
```

</details>

#### converts to minutes

- converts to minutes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to minutes")
val ns = 60000000000
expect ns > 1000000
```

</details>

#### converts to hours

- converts to hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to hours")
val ns = 3600000000000
expect ns > 60000000000
```

</details>

#### converts to days

- converts to days


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to days")
val ns = 86400000000000
expect ns > 3600000000000
```

</details>

#### duration arithmetic

#### adds durations

- adds durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds durations")
val a = 1000000000
val b = 2000000000
expect (a + b) == 3000000000
```

</details>

#### subtracts durations

- subtracts durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtracts durations")
val a = 3000000000
val b = 1000000000
expect (a - b) == 2000000000
```

</details>

#### multiplies duration

- multiplies duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplies duration")
val dur = 1000000000
val n = 2
expect (dur * n) == 2000000000
```

</details>

#### time duration constants

#### uses millisecond constant

- uses millisecond constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses millisecond constant")
val ms = 1000000
expect ms > 0
```

</details>

#### uses second constant

- uses second constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses second constant")
val s = 1000000000
expect s > 1000000
```

</details>

#### uses minute constant

- uses minute constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses minute constant")
val m = 60000000000
expect m > 1000000000
```

</details>

#### uses hour constant

- uses hour constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses hour constant")
val h = 3600000000000
expect h > 60000000000
```

</details>

#### uses day constant

- uses day constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses day constant")
val d = 86400000000000
expect d > 3600000000000
```

</details>

#### duration comparisons

#### compares time durations

- compares time durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares time durations")
val fast = 1000
val slow = 2000
expect slow > fast
```

</details>

#### equality of durations

- equality of durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equality of durations")
val a = 1000000000
val b = 1000000000
expect a == b
```

</details>

#### less than comparisons

- less than comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less than comparisons")
val a = 1000000000
val b = 2000000000
expect a < b
```

</details>

#### f32 duration conversions

#### converts to seconds with precision

- converts to seconds with precision


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to seconds with precision")
val ns = 1500000000
# 1.5 seconds in nanoseconds
expect ns > 1000000000
```

</details>

#### converts to milliseconds with precision

- converts to milliseconds with precision


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to milliseconds with precision")
val ns = 1500000
# 1.5 milliseconds in nanoseconds
expect ns > 1000000
```

</details>

### Combined Unit Operations

#### mixed operations

#### size and time are independent units

- size and time are independent units


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("size and time are independent units")
val bytes = 1024
val nanos = 1000000000
expect bytes < nanos
```

</details>

#### arithmetic with same unit types

- arithmetic with same unit types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arithmetic with same unit types")
val bytes1 = 2000
val bytes2 = 1000
val total = bytes1 + bytes2
expect total == 3000
```

</details>

#### time arithmetic operations

- time arithmetic operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("time arithmetic operations")
val start = 1000000000
val end = 2000000000
val elapsed = end - start
expect elapsed == 1000000000
```

</details>

#### unit identity

#### units preserve type safety

- units preserve type safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("units preserve type safety")
val size = 1024
val time = 1000000
expect size > 0
expect time > 0
```

</details>

#### multiple unit values

- multiple unit values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple unit values")
val b = 2048
val t = 2000000000
expect (b + 1024) == 3072
expect (t + 1000000000) == 3000000000
```

</details>

### Edge Cases and Boundaries

#### zero values

#### handles zero size

- handles zero size


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero size")
val zero = 0
expect zero == 0
expect zero < 1
```

</details>

#### handles zero duration

- handles zero duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero duration")
val zero = 0
expect zero == 0
expect zero < 1
```

</details>

#### large values

#### handles large byte counts

- handles large byte counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large byte counts")
val large = 1099511627776
expect large > 0
expect large > 1000000000
```

</details>

#### handles large durations

- handles large durations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles large durations")
val large = 86400000000000
expect large > 0
expect large > 1000000000
```

</details>

#### unit overflow handling

#### arithmetic results are valid

- arithmetic results are valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arithmetic results are valid")
val a = 999999999
val b = 1
val res_val = a + b
expect res_val == 1000000000
```

</details>

#### subtraction boundaries

- subtraction boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subtraction boundaries")
val a = 1000
val b = 1000
val res_val = a - b
expect res_val == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/units/units_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Size Units, Time Units, Combined Unit Operations, Edge Cases and Boundaries.
- Size Units
- Time Units
- Combined Unit Operations
- Edge Cases and Boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
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

- Canonical SPipe generation for source `178441b1c9d479acec80936a8c1a76ae9af1f7585401ad2e56dba6124ee9538d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `178441b1c9d479acec80936a8c1a76ae9af1f7585401ad2e56dba6124ee9538d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `178441b1c9d479acec80936a8c1a76ae9af1f7585401ad2e56dba6124ee9538d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/units/units_spec.spl
mirror: doc/06_spec/unit/lib/common/units/units_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/units/units_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/units/units_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/units/units_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates ByteCount from integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/units/units_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ByteCount zero value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/units/units_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ByteCount comparisons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
