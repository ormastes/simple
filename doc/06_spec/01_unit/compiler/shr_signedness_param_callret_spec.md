# Shr Signedness Param Callret Specification

> Tests covering right-shift signedness — param + call-return paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shr Signedness Param Callret Specification

## Scenarios

### right-shift signedness — param + call-return paths

#### signed param: shr_signed_param(-16) yields -8

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- signed param: shr_signed_param(-16) yields -8
   - Expected: got equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("signed param: shr_signed_param(-16) yields -8")
val got: i32 = shr_signed_param(-16)
expect(got).to_equal(-8)
```

</details>

#### unsigned param: shr_unsigned_param(2147483648) yields 1073741824

- unsigned param: shr_unsigned_param(2147483648) yields 1073741824
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsigned param: shr_unsigned_param(2147483648) yields 1073741824")
val got: u32 = shr_unsigned_param(2147483648 as u32)
val expected: u32 = 1073741824 as u32
expect(got).to_equal(expected)
```

</details>

#### signed call-return: get_neg_sixteen() >> 1 yields -8

- signed call-return: get_neg_sixteen() >> 1 yields -8
   - Expected: got equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("signed call-return: get_neg_sixteen() >> 1 yields -8")
val v: i32 = get_neg_sixteen()
val got: i32 = v >> 1
expect(got).to_equal(-8)
```

</details>

#### unsigned call-return: get_high_bit() >> 1 yields 1073741824

- unsigned call-return: get_high_bit() >> 1 yields 1073741824
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsigned call-return: get_high_bit() >> 1 yields 1073741824")
val v: u32 = get_high_bit()
val got: u32 = v >> 1
val expected: u32 = 1073741824 as u32
expect(got).to_equal(expected)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shr_signedness_param_callret_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering right-shift signedness — param + call-return paths.
- right-shift signedness — param + call-return paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d531fd13aa3f083d2e237b32aab6d66075c02cb30d98c832b7ea792dee169fa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d531fd13aa3f083d2e237b32aab6d66075c02cb30d98c832b7ea792dee169fa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d531fd13aa3f083d2e237b32aab6d66075c02cb30d98c832b7ea792dee169fa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/shr_signedness_param_callret_spec.spl
mirror: doc/06_spec/01_unit/compiler/shr_signedness_param_callret_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/shr_signedness_param_callret_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/shr_signedness_param_callret_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/shr_signedness_param_callret_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/shr_signedness_param_callret_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signed param: shr_signed_param(-16) yields -8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shr_signedness_param_callret_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unsigned param: shr_unsigned_param(2147483648) yields 1073741824' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shr_signedness_param_callret_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signed call-return: get_neg_sixteen() >> 1 yields -8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
