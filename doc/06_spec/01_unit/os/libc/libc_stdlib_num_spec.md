# Libc Stdlib Num Specification

> Tests covering SimpleOS libc stdlib numeric (integer), libc_strtoul — unsigned parse, libc_strtoll — signed parse, libc_strtoull — unsigned long long, libc_div — integer division, libc_ldiv — long division, libc_lldiv — long long division, libc_rand_next — LCG pseudorandom.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libc Stdlib Num Specification

## Scenarios

### SimpleOS libc stdlib numeric (integer)

### libc_strtoul — unsigned parse

#### parses simple decimal
#### parses hex with 0x prefix auto-detect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("0xFF".bytes(), 0)).to_equal(255)
```

</details>

#### parses octal with 0 prefix auto-detect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("017".bytes(), 0)).to_equal(15)
```

</details>

#### parses decimal with base 0 (no prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("42".bytes(), 0)).to_equal(42)
```

</details>

#### skips leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("  42".bytes(), 10)).to_equal(42)
```

</details>

#### stops at first non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("42abc".bytes(), 10)).to_equal(42)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("".bytes(), 10)).to_equal(0)
```

</details>

#### handles non-numeric input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("abc".bytes(), 10)).to_equal(0)
```

</details>

#### parses base 16 explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("FF".bytes(), 16)).to_equal(255)
```

</details>

#### parses base 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("1010".bytes(), 2)).to_equal(10)
```

</details>

#### accepts a leading minus and negates (C-conformant)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("-1".bytes(), 10)).to_equal(-1)
```

</details>

#### accepts a leading plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("+5".bytes(), 10)).to_equal(5)
```

</details>

#### base-0 bare zero is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("0".bytes(), 0)).to_equal(0)
```

</details>

#### base-0 '0x' with no hex digit is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("0x".bytes(), 0)).to_equal(0)
```

</details>

#### base-0 '08' stops at invalid octal digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoul("08".bytes(), 0)).to_equal(0)
```

</details>

### libc_strtoll — signed parse

#### parses simple decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("123".bytes(), 10)).to_equal(123)
```

</details>

#### parses negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("-42".bytes(), 10)).to_equal(-42)
```

</details>

#### parses positive sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("+42".bytes(), 10)).to_equal(42)
```

</details>

#### parses negative hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("-0xFF".bytes(), 0)).to_equal(-255)
```

</details>

#### skips leading whitespace with sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("  -42".bytes(), 10)).to_equal(-42)
```

</details>

#### stops at first non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("-42xyz".bytes(), 10)).to_equal(-42)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("".bytes(), 10)).to_equal(0)
```

</details>

#### parses negative octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoll("-017".bytes(), 0)).to_equal(-15)
```

</details>

### libc_strtoull — unsigned long long

#### parses simple decimal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoull("123".bytes(), 10)).to_equal(123)
```

</details>

#### parses hex with auto-detect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoull("0xFF".bytes(), 0)).to_equal(255)
```

</details>

#### large value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libc_strtoull("1234567890".bytes(), 10)).to_equal(1234567890)
```

</details>

### libc_div — integer division

#### divides positive by positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(7, 2)
expect(result.quot).to_equal(3)
expect(result.rem).to_equal(1)
```

</details>

#### divides negative by positive (toward zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(-7, 2)
expect(result.quot).to_equal(-3)
expect(result.rem).to_equal(-1)
```

</details>

#### divides positive by negative (toward zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(7, -2)
expect(result.quot).to_equal(-3)
expect(result.rem).to_equal(1)
```

</details>

#### divides negative by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(-7, -2)
expect(result.quot).to_equal(3)
expect(result.rem).to_equal(-1)
```

</details>

#### exact division has zero remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(10, 2)
expect(result.quot).to_equal(5)
expect(result.rem).to_equal(0)
```

</details>

#### handles zero numerator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_div(0, 5)
expect(result.quot).to_equal(0)
expect(result.rem).to_equal(0)
```

</details>

### libc_ldiv — long division

#### long divide matches div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_ldiv(7, 2)
expect(result.quot).to_equal(3)
expect(result.rem).to_equal(1)
```

</details>

#### large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_ldiv(1000000000, 3)
expect(result.quot).to_equal(333333333)
```

</details>

### libc_lldiv — long long division

#### long long divide matches div

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_lldiv(7, 2)
expect(result.quot).to_equal(3)
expect(result.rem).to_equal(1)
```

</details>

#### large dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = libc_lldiv(123456789, 12)
expect(result.quot).to_equal(10288065)
```

</details>

### libc_rand_next — LCG pseudorandom

#### deterministic: same input state yields same output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = libc_rand_next(12345)
val r2 = libc_rand_next(12345)
expect(r1.state).to_equal(r2.state)
expect(r1.value).to_equal(r2.value)
```

</details>

#### produces non-zero values from seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = libc_rand_next(12345)
expect(r.state).to_be_greater_than(0)
expect(r.value).to_be_greater_than(0)
```

</details>

#### value is always in range 0..32767

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = 12345
var i = 0
while i < 10:
    val r = libc_rand_next(state)
    expect(r.value).to_be_greater_than(-1)
    expect(r.value).to_be_less_than(32768)
    state = r.state
    i = i + 1
```

</details>

#### chain produces different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = libc_rand_next(42)
val r2 = libc_rand_next(r1.state)
expect(r2.value).to_be_greater_than(-1)
expect(r2.value).to_be_less_than(32768)
```

</details>

#### different seeds produce different sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = libc_rand_next(100).state
val s2 = libc_rand_next(200).state
expect(s1).to_not_equal(s2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/libc/libc_stdlib_num_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS libc stdlib numeric (integer), libc_strtoul — unsigned parse, libc_strtoll — signed parse, libc_strtoull — unsigned long long, libc_div — integer division, libc_ldiv — long division, libc_lldiv — long long division, libc_rand_next — LCG pseudorandom.
- SimpleOS libc stdlib numeric (integer)
- libc_strtoul — unsigned parse
- libc_strtoll — signed parse
- libc_strtoull — unsigned long long
- libc_div — integer division
- libc_ldiv — long division
- libc_lldiv — long long division
- libc_rand_next — LCG pseudorandom

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `74f127ae43a6bc22185469b9a860220c577a7b8a4fecec0fcb19d472fbd92af3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74f127ae43a6bc22185469b9a860220c577a7b8a4fecec0fcb19d472fbd92af3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74f127ae43a6bc22185469b9a860220c577a7b8a4fecec0fcb19d472fbd92af3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/libc/libc_stdlib_num_spec.spl
mirror: doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/libc/libc_stdlib_num_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 43 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:24:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses simple decimal' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses hex with 0x prefix auto-detect' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses octal with 0 prefix auto-detect' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/libc/libc_stdlib_num_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses decimal with base 0 (no prefix)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
