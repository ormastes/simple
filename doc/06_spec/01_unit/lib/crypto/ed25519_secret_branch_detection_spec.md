# Ed25519 Secret Branch Detection Specification

> Tests covering Ed25519: no scalar-multiplication path branches on secret material.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Secret Branch Detection Specification

## Scenarios

### Ed25519: no scalar-multiplication path branches on secret material

#### the module under audit is readable and non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### ed_scalar_mul has no data-dependent branch on the scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text(SRC_PATH)
val body = _fn_body(src, "fn ed_scalar_mul(scalar: [u8], p: EdPoint) -> EdPoint:")
expect(body.len() > 0u64).to_be(true)
expect(_secret_branch_count(body)).to_equal(0u64)
```

</details>

#### ed_scalar_mul_basepoint has no data-dependent branch on the scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is the entry point signing actually calls.
val src = rt_file_read_text(SRC_PATH)
val body = _fn_body(src, "fn ed_scalar_mul_basepoint(scalar: [u8]) -> EdPoint:")
expect(body.len() > 0u64).to_be(true)
expect(_secret_branch_count(body)).to_equal(0u64)
```

</details>

#### ed_scalar_mul_basepoint_simple has no data-dependent branch on the scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The delegate that carried the actual side channel while the
# documented constant-time function sat unused.
val src = rt_file_read_text(SRC_PATH)
val body = _fn_body(src, "fn ed_scalar_mul_basepoint_simple(scalar: [u8]) -> EdPoint:")
expect(body.len() > 0u64).to_be(true)
expect(_secret_branch_count(body)).to_equal(0u64)
```

</details>

#### the detector itself fires on a known-branchful body (anti-vacuity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If this ever returns 0 the three checks above prove nothing.
val fake = "\n    if _ed_scalar_bit(scalar, bit_idx) == 1:\n        result = base\n"
expect(_secret_branch_count(fake)).to_equal(1u64)
val clean = "\n    result = ed_point_add(result, sel)\n"
expect(_secret_branch_count(clean)).to_equal(0u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ed25519: no scalar-multiplication path branches on secret material.
- Ed25519: no scalar-multiplication path branches on secret material

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `e00fce15a864c5427b687b70d5a4c986aba8be47a13e46d19ff87d043df9acf7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e00fce15a864c5427b687b70d5a4c986aba8be47a13e46d19ff87d043df9acf7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e00fce15a864c5427b687b70d5a4c986aba8be47a13e46d19ff87d043df9acf7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl:72:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'the module under audit is readable and non-empty' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl:82:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ed_scalar_mul has no data-dependent branch on the scalar' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl:88:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ed_scalar_mul_basepoint has no data-dependent branch on the scalar' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/crypto/ed25519_secret_branch_detection_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ed_scalar_mul_basepoint_simple has no data-dependent branch on the scalar' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
