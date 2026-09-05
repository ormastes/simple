# Limb Spike Specification

> Tests covering math.bignum.limb, limb_mul, add_limbs, sub_limbs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Limb Spike Specification

## Scenarios

### math.bignum.limb

### limb_mul

#### LIMB_MASK^2 = (1, LIMB_BASE - 2)

- LIMB_MASK^2 = (1, LIMB_BASE - 2)
   - Expected: r[0] equals `1`
   - Expected: r[1] equals `LIMB_BASE - 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LIMB_MASK^2 = (1, LIMB_BASE - 2)")
# (2^30 - 1)^2 = 2^60 - 2^31 + 1
#              = (2^30 - 2) * 2^30 + 1
# so low limb = 1, high limb = LIMB_BASE - 2.
val r = limb_mul(LIMB_MASK, LIMB_MASK)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(LIMB_BASE - 2)
```

</details>

### add_limbs

#### carries at LIMB_BASE

- carries at LIMB_BASE
   - Expected: r[0] equals `0`
   - Expected: r[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries at LIMB_BASE")
# LIMB_MASK + 1 = LIMB_BASE -> carry out, limb 0.
val r = add_limbs(LIMB_MASK, 1, 0)
expect(r[0]).to_equal(0)
expect(r[1]).to_equal(1)
```

</details>

### sub_limbs

#### borrows when a < b

- borrows when a < b
   - Expected: r[0] equals `LIMB_MASK`
   - Expected: r[1] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("borrows when a < b")
# 0 - 1 = LIMB_MASK with borrow_out 1.
val r = sub_limbs(0, 1, 0)
expect(r[0]).to_equal(LIMB_MASK)
expect(r[1]).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/math/bignum/limb_spike_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering math.bignum.limb, limb_mul, add_limbs, sub_limbs.
- math.bignum.limb
- limb_mul
- add_limbs
- sub_limbs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `66a2fa3f2bbba3012afcdfb1fff2abd7b655079c396078bf450d4b9e27597751`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66a2fa3f2bbba3012afcdfb1fff2abd7b655079c396078bf450d4b9e27597751`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66a2fa3f2bbba3012afcdfb1fff2abd7b655079c396078bf450d4b9e27597751`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/math/bignum/limb_spike_spec.spl
mirror: doc/06_spec/unit/lib/math/bignum/limb_spike_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/math/bignum/limb_spike_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/math/bignum/limb_spike_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/math/bignum/limb_spike_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/math/bignum/limb_spike_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LIMB_MASK^2 = (1, LIMB_BASE - 2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/bignum/limb_spike_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries at LIMB_BASE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/math/bignum/limb_spike_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'borrows when a < b' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
