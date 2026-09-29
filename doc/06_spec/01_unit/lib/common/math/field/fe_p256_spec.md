# Fe P256 Specification

> Tests covering fe_p256 field arithmetic (P-256).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fe P256 Specification

## Scenarios

### fe_p256 field arithmetic (P-256)

#### the module named by p256.spl and ecdh_p256.spl actually loads

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### round-trips a 32-byte big-endian value through from/to bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gx = fe_from_bytes(GX_BYTES)
val out = fe_to_bytes(gx)
expect(out.len()).to_equal(32u64)
var i: u64 = 0
var same = true
while i < 32:
    if out[i] != GX_BYTES[i]:
        same = false
    i = i + 1
expect(same).to_be(true)
```

</details>

#### add and sub are inverse, and a - a is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gx = fe_from_bytes(GX_BYTES)
val gy = fe_from_bytes(GY_BYTES)
expect(fe_eq(fe_sub(fe_add(gx, gy), gy), gx)).to_be(true)
expect(fe_eq(fe_sub(gx, gx), fe_zero())).to_be(true)
expect(fe_eq(fe_add(gx, fe_sub(fe_zero(), gx)), fe_zero())).to_be(true)
```

</details>

#### small-value multiplication agrees with plain integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 7 * 9 = 63, well below p so no reduction is involved.
expect(fe_eq(fe_mul(_small(7u64), _small(9u64)), _small(63u64))).to_be(true)
expect(fe_eq(fe_sq(_small(65535u64)), _small(4294836225u64))).to_be(true)
expect(fe_eq(fe_mul(_small(1u64), _small(0u64)), fe_zero())).to_be(true)
```

</details>

#### multiplication really reduces: (p-1)^2 == 1 mod p

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p_minus_1 = fe_sub(fe_zero(), fe_one())
expect(fe_eq(fe_sq(p_minus_1), fe_one())).to_be(true)
```

</details>

#### the generator satisfies the curve equation y^2 = x^3 - 3x + b

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is the strongest available check on fe_mul's reduction: it is
# an identity over the full 256-bit range that only holds if the
# Solinas reduction is exactly right.
val x = fe_from_bytes(GX_BYTES)
val y = fe_from_bytes(GY_BYTES)
val b = fe_from_bytes(B_BYTES)
val lhs = fe_sq(y)
val three_x = fe_add(fe_add(x, x), x)
val rhs = fe_add(fe_sub(fe_mul(fe_sq(x), x), three_x), b)
expect(fe_eq(lhs, rhs)).to_be(true)
```

</details>

#### fe_inv returns a true modular inverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = fe_from_bytes(GX_BYTES)
expect(fe_eq(fe_mul(x, fe_inv(x)), fe_one())).to_be(true)
expect(fe_eq(fe_mul(_small(2u64), fe_inv(_small(2u64))), fe_one())).to_be(true)
```

</details>

#### fe_cond_select picks by the mask bit without branching on values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = _small(11u64)
val b = _small(22u64)
expect(fe_eq(fe_cond_select(a, b, 0u64), a)).to_be(true)
expect(fe_eq(fe_cond_select(a, b, 1u64), b)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math/field/fe_p256_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fe_p256 field arithmetic (P-256).
- fe_p256 field arithmetic (P-256)

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

- Canonical SPipe generation for source `4927f81a70739cd09c4b6ae5c13de67a43eb218937045ba38bb0a9c610f42fcc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4927f81a70739cd09c4b6ae5c13de67a43eb218937045ba38bb0a9c610f42fcc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4927f81a70739cd09c4b6ae5c13de67a43eb218937045ba38bb0a9c610f42fcc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/math/field/fe_p256_spec.spl
mirror: doc/06_spec/01_unit/lib/common/math/field/fe_p256_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/math/field/fe_p256_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/math/field/fe_p256_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/math/field/fe_p256_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/math/field/fe_p256_spec.spl:57:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'the module named by p256.spl and ecdh_p256.spl actually loads' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/math/field/fe_p256_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips a 32-byte big-endian value through from/to bytes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/math/field/fe_p256_spec.spl:76:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'add and sub are inverse, and a - a is zero' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/math/field/fe_p256_spec.spl:83:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'small-value multiplication agrees with plain integers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
