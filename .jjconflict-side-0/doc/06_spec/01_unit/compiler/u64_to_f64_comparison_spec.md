# U64 To F64 Comparison Specification

> Tests covering u64 vs f64 comparison uses unsigned int->float conversion, signed i64 vs f64 comparison is unchanged (negatives stay negative).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 To F64 Comparison Specification

## Scenarios

### u64 vs f64 comparison uses unsigned int->float conversion

#### 2^63 compares as a positive number against f64

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 2^63 compares as a positive number against f64
   - Expected: high > 0.0 is true
   - Expected: 0.0 < high is true
   - Expected: high < 9223372036854775808.0 is false
   - Expected: high <= 9223372036854775808.0 is true
   - Expected: high >= 9223372036854775808.0 is true
   - Expected: high == 9223372036854775808.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2^63 compares as a positive number against f64")
val high: u64 = 0x8000000000000000u64
expect(high > 0.0).to_equal(true)
expect(0.0 < high).to_equal(true)
expect(high < 9223372036854775808.0).to_equal(false)
expect(high <= 9223372036854775808.0).to_equal(true)
expect(high >= 9223372036854775808.0).to_equal(true)
expect(high == 9223372036854775808.0).to_equal(true)
```

</details>

#### 2^63+1 compares as a positive number against f64

- 2^63+1 compares as a positive number against f64
   - Expected: h1 > 0.0 is true
   - Expected: h1 >= 9223372036854775808.0 is true
   - Expected: 0.0 < h1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("2^63+1 compares as a positive number against f64")
val h1: u64 = 0x8000000000000001u64
expect(h1 > 0.0).to_equal(true)
expect(h1 >= 9223372036854775808.0).to_equal(true)
expect(0.0 < h1).to_equal(true)
```

</details>

#### u64::MAX compares as a large positive number against f64

- u64::MAX compares as a large positive number against f64
   - Expected: umax > 0.0 is true
   - Expected: umax > 9000000000000000000.0 is true
   - Expected: 0.0 < umax is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("u64::MAX compares as a large positive number against f64")
val umax: u64 = 0xFFFFFFFFFFFFFFFFu64
expect(umax > 0.0).to_equal(true)
expect(umax > 9000000000000000000.0).to_equal(true)
expect(0.0 < umax).to_equal(true)
```

</details>

#### mixed u64/f64 arithmetic promotes the u64 as unsigned

- mixed u64/f64 arithmetic promotes the u64 as unsigned
   - Expected: high + 0.0 > 0.0 is true
   - Expected: high - 1.0 > 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mixed u64/f64 arithmetic promotes the u64 as unsigned")
val high: u64 = 0x8000000000000000u64
expect(high + 0.0 > 0.0).to_equal(true)
expect(high - 1.0 > 0.0).to_equal(true)
```

</details>

### signed i64 vs f64 comparison is unchanged (negatives stay negative)

#### negative i64 compares as negative against f64

- negative i64 compares as negative against f64
   - Expected: neg < 0.0 is true
   - Expected: 0.0 > neg is true
   - Expected: neg > -10.0 is true
   - Expected: neg == -5.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative i64 compares as negative against f64")
val neg: i64 = -5
expect(neg < 0.0).to_equal(true)
expect(0.0 > neg).to_equal(true)
expect(neg > -10.0).to_equal(true)
expect(neg == -5.0).to_equal(true)
```

</details>

#### positive i64 in the shared range is unaffected

- positive i64 in the shared range is unaffected
   - Expected: pos > 0.0 is true
   - Expected: pos < 100.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive i64 in the shared range is unaffected")
val pos: i64 = 42
expect(pos > 0.0).to_equal(true)
expect(pos < 100.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u64_to_f64_comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering u64 vs f64 comparison uses unsigned int->float conversion, signed i64 vs f64 comparison is unchanged (negatives stay negative).
- u64 vs f64 comparison uses unsigned int->float conversion
- signed i64 vs f64 comparison is unchanged (negatives stay negative)

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

- Canonical SPipe generation for source `d54b86c72eeca14394cec7b502e2a587ce2b3415e7178ba01e9b40db9cc96ec7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d54b86c72eeca14394cec7b502e2a587ce2b3415e7178ba01e9b40db9cc96ec7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d54b86c72eeca14394cec7b502e2a587ce2b3415e7178ba01e9b40db9cc96ec7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/u64_to_f64_comparison_spec.spl
mirror: doc/06_spec/01_unit/compiler/u64_to_f64_comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/u64_to_f64_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/u64_to_f64_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/u64_to_f64_comparison_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '2^63 compares as a positive number against f64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u64_to_f64_comparison_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '2^63+1 compares as a positive number against f64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/u64_to_f64_comparison_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'u64::MAX compares as a large positive number against f64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
