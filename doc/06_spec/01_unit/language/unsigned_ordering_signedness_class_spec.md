# Unsigned Ordering Signedness Class Specification

> Tests covering unsigned ordering is signedness-correct across the whole operator class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsigned Ordering Signedness Class Specification

## Scenarios

### unsigned ordering is signedness-correct across the whole operator class

#### handles all four ordering operators at the 2^63 boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles all four ordering operators at the 2^63 boundary
   - Expected: big > zero is true
   - Expected: big >= zero is true
   - Expected: big < zero is false
   - Expected: big <= zero is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all four ordering operators at the 2^63 boundary")
val big: u64 = 9223372036854775808u64
val zero: u64 = 0u64
expect(big > zero).to_equal(true)
expect(big >= zero).to_equal(true)
expect(big < zero).to_equal(false)
expect(big <= zero).to_equal(false)
```

</details>

#### handles a high-bit u64 against an UNSUFFIXED signed literal

- handles a high-bit u64 against an UNSUFFIXED signed literal
   - Expected: big > 0 is true
   - Expected: big >= 1 is true
   - Expected: big < 0 is false
   - Expected: big <= 1 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a high-bit u64 against an UNSUFFIXED signed literal")
# `0` here is a signed Int, not a u64 -- the mixed pairing. A UInt/UInt
# only fix leaves this arm reinterpreting the u64 as negative.
val big: u64 = 9223372036854775808u64
expect(big > 0).to_equal(true)
expect(big >= 1).to_equal(true)
expect(big < 0).to_equal(false)
expect(big <= 1).to_equal(false)
```

</details>

#### handles the signed literal on the LEFT (operand order is not symmetric in code)

- handles the signed literal on the LEFT (operand order is not symmetric in code)
   - Expected: 0 < big is true
   - Expected: 0 <= big is true
   - Expected: 0 > big is false
   - Expected: 0 >= big is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles the signed literal on the LEFT (operand order is not symmetric in code)")
val big: u64 = 9223372036854775808u64
expect(0 < big).to_equal(true)
expect(0 <= big).to_equal(true)
expect(0 > big).to_equal(false)
expect(0 >= big).to_equal(false)
```

</details>

#### orders correctly at u64 MAX, not just at the 2^63 threshold

- orders correctly at u64 MAX, not just at the 2^63 threshold
   - Expected: maxv > big is true
   - Expected: maxv >= maxv is true
   - Expected: maxv < big is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders correctly at u64 MAX, not just at the 2^63 threshold")
val maxv: u64 = 18446744073709551615u64
val big: u64 = 9223372036854775808u64
expect(maxv > big).to_equal(true)
expect(maxv >= maxv).to_equal(true)
expect(maxv < big).to_equal(false)
```

</details>

#### keeps a strictly increasing high-bit sequence ordered

- keeps a strictly increasing high-bit sequence ordered
   - Expected: a < b is true
   - Expected: b < c is true
   - Expected: a < c is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a strictly increasing high-bit sequence ordered")
# Signed reinterpretation wraps this sequence into DEcreasing order,
# so a single monotonicity walk catches any arm that still casts.
val a: u64 = 9223372036854775807u64
val b: u64 = 9223372036854775808u64
val c: u64 = 18446744073709551615u64
expect(a < b).to_equal(true)
expect(b < c).to_equal(true)
expect(a < c).to_equal(true)
```

</details>

#### keeps < and > mutually consistent for every high-bit pair

- keeps < and > mutually consistent for every high-bit pair
   - Expected: a < c is true
   - Expected: c < a is false
   - Expected: c > a is true
   - Expected: a > c is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps < and > mutually consistent for every high-bit pair")
val a: u64 = 9223372036854775807u64
val c: u64 = 18446744073709551615u64
# If any one arm were still signed, these two would BOTH report true.
expect(a < c).to_equal(true)
expect(c < a).to_equal(false)
expect(c > a).to_equal(true)
expect(a > c).to_equal(false)
```

</details>

#### leaves ordinary signed comparison, including negatives, untouched

- leaves ordinary signed comparison, including negatives, untouched
   - Expected: -5 < 3 is true
   - Expected: -5 > 3 is false
   - Expected: 3 >= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves ordinary signed comparison, including negatives, untouched")
# Guards the fix against over-reach: it must not capture Int/Int.
expect(-5 < 3).to_equal(true)
expect(-5 > 3).to_equal(false)
expect(3 >= 3).to_equal(true)
```

</details>

#### orders a negative signed value below any unsigned value

- orders a negative signed value below any unsigned value
   - Expected: -1 < big is true
   - Expected: big > -1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a negative signed value below any unsigned value")
# The one pairing with no Rust-native answer, so it is hand-written and
# therefore the most likely to be got wrong.
val big: u64 = 9223372036854775808u64
expect(-1 < big).to_equal(true)
expect(big > -1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/unsigned_ordering_signedness_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unsigned ordering is signedness-correct across the whole operator class.
- unsigned ordering is signedness-correct across the whole operator class

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `b8a2e5907ae9663757125a02cdf0cc1e7702e2a499f6acf11e1b7b780df60a51`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8a2e5907ae9663757125a02cdf0cc1e7702e2a499f6acf11e1b7b780df60a51`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8a2e5907ae9663757125a02cdf0cc1e7702e2a499f6acf11e1b7b780df60a51`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/unsigned_ordering_signedness_class_spec.spl
mirror: doc/06_spec/01_unit/language/unsigned_ordering_signedness_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/unsigned_ordering_signedness_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/unsigned_ordering_signedness_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/unsigned_ordering_signedness_class_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles all four ordering operators at the 2^63 boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/unsigned_ordering_signedness_class_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles a high-bit u64 against an UNSUFFIXED signed literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/unsigned_ordering_signedness_class_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles the signed literal on the LEFT (operand order is not symmetric in code)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
