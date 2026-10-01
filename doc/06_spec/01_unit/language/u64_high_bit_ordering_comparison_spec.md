# U64 High Bit Ordering Comparison Specification

> Tests covering u64 values at or above 2^63 under the interpreter's ordering operators.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 High Bit Ordering Comparison Specification

## Scenarios

### u64 values at or above 2^63 under the interpreter's ordering operators

#### compares a high-bit u64 as unsigned, not as a negative i64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compares a high-bit u64 as unsigned, not as a negative i64
   - Expected: big > 0u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares a high-bit u64 as unsigned, not as a negative i64")
# 2^63 exactly -- the threshold the bug doc pinned.
val big: u64 = 9223372036854775808u64
expect(big > 0u64).to_equal(true)
```

</details>

#### still compares a below-threshold u64 correctly (negative control)

- still compares a below-threshold u64 correctly (negative control)
   - Expected: small > 0u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still compares a below-threshold u64 correctly (negative control)")
val small: u64 = 9223372036854775807u64
expect(small > 0u64).to_equal(true)
```

</details>

#### orders a high-bit u64 above a below-threshold one

- orders a high-bit u64 above a below-threshold one
   - Expected: big > small is true
   - Expected: big < small is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders a high-bit u64 above a below-threshold one")
val small: u64 = 9223372036854775807u64
val big: u64 = 9223372036854775808u64
expect(big > small).to_equal(true)
expect(big < small).to_equal(false)
```

</details>

#### preserves the stored high-bit value through to_text (never was corrupt)

- preserves the stored high-bit value through to_text (never was corrupt)
   - Expected: big.to_text() equals `9223372036854775808`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the stored high-bit value through to_text (never was corrupt)")
val big: u64 = 9223372036854775808u64
expect(big.to_text()).to_equal("9223372036854775808")
```

</details>

#### narrows the Option returned past a high-bit u64 guard (doc reproducer)

- narrows the Option returned past a high-bit u64 guard (doc reproducer)
   - Expected: got != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrows the Option returned past a high-bit u64 guard (doc reproducer)")
# This is the doc's original observation site. It fails only because the
# `frame.checksum > 0u64` guard inside `find_valid` mis-compares.
val big = [Frame(id: "a", checksum: 9223372036854775808u64)]
val got = find_valid(big, "a")
expect(got != nil).to_equal(true)
```

</details>

#### narrows for a below-threshold checksum (negative control)

- narrows for a below-threshold checksum (negative control)
   - Expected: got != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrows for a below-threshold checksum (negative control)")
val small = [Frame(id: "a", checksum: 9223372036854775807u64)]
val got = find_valid(small, "a")
expect(got != nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering u64 values at or above 2^63 under the interpreter's ordering operators.
- u64 values at or above 2^63 under the interpreter's ordering operators

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `2d3bf7c803c9c4370772b1c4d8366bcddc432396af11c936d7ff228f10d5d817`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d3bf7c803c9c4370772b1c4d8366bcddc432396af11c936d7ff228f10d5d817`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d3bf7c803c9c4370772b1c4d8366bcddc432396af11c936d7ff228f10d5d817`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl
mirror: doc/06_spec/01_unit/language/u64_high_bit_ordering_comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/u64_high_bit_ordering_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/u64_high_bit_ordering_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares a high-bit u64 as unsigned, not as a negative i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still compares a below-threshold u64 correctly (negative control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders a high-bit u64 above a below-threshold one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
