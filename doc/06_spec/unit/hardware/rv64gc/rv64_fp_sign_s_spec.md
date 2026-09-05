# RV64 Single-Precision FP Sign Manipulation Tests

> Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Sign Manipulation Tests

Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-SIGN-S-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fsgnj.s, fsgnjn.s, fsgnjx.s.

## Scenarios

### FSGNJ.S (copy sign from rs2)

#### positive + positive = positive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- positive + positive = positive
   - Expected: fp_sgnj_s(ONE_S, TWO_S) equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive + positive = positive")
expect(fp_sgnj_s(ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

#### positive + negative = negative

- positive + negative = negative
   - Expected: fp_sgnj_s(ONE_S, NEG_TWO_S) equals `NEG_ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive + negative = negative")
expect(fp_sgnj_s(ONE_S, NEG_TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### negative + positive = positive

- negative + positive = positive
   - Expected: fp_sgnj_s(NEG_ONE_S, TWO_S) equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative + positive = positive")
expect(fp_sgnj_s(NEG_ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

### FSGNJN.S (copy negated sign from rs2)

#### positive + positive = negative

- positive + positive = negative
   - Expected: fp_sgnjn_s(ONE_S, TWO_S) equals `NEG_ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive + positive = negative")
expect(fp_sgnjn_s(ONE_S, TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### positive + negative = positive

- positive + negative = positive
   - Expected: fp_sgnjn_s(ONE_S, NEG_TWO_S) equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive + negative = positive")
expect(fp_sgnjn_s(ONE_S, NEG_TWO_S)).to_equal(ONE_S)
```

</details>

#### negative + positive = negative

- negative + positive = negative
   - Expected: fp_sgnjn_s(NEG_ONE_S, TWO_S) equals `NEG_ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative + positive = negative")
expect(fp_sgnjn_s(NEG_ONE_S, TWO_S)).to_equal(NEG_ONE_S)
```

</details>

### FSGNJX.S (XOR signs)

#### positive XOR positive = positive

- positive XOR positive = positive
   - Expected: fp_sgnjx_s(ONE_S, TWO_S) equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive XOR positive = positive")
expect(fp_sgnjx_s(ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

#### positive XOR negative = negative

- positive XOR negative = negative
   - Expected: fp_sgnjx_s(ONE_S, NEG_TWO_S) equals `NEG_ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive XOR negative = negative")
expect(fp_sgnjx_s(ONE_S, NEG_TWO_S)).to_equal(NEG_ONE_S)
```

</details>

#### negative XOR negative = positive

- negative XOR negative = positive
   - Expected: fp_sgnjx_s(NEG_ONE_S, NEG_TWO_S) equals `ONE_S`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative XOR negative = positive")
expect(fp_sgnjx_s(NEG_ONE_S, NEG_TWO_S)).to_equal(ONE_S)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9dc22f5cd674d992a3c6ff109a2ac15751eb93c605a5021eaaef927468783593`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dc22f5cd674d992a3c6ff109a2ac15751eb93c605a5021eaaef927468783593`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dc22f5cd674d992a3c6ff109a2ac15751eb93c605a5021eaaef927468783593`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_fp_sign_s_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_fp_sign_s_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_fp_sign_s_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive + positive = positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'positive + negative = negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_fp_sign_s_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negative + positive = positive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
