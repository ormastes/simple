# Ed25519 Field Ops Specification

> Tests covering Ed25519 field and base-point primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Field Ops Specification

## Scenarios

### Ed25519 field and base-point primitives

#### encodes the field identity as canonical little-endian one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes the field identity as canonical little-endian one
   - Expected: fe_to_bytes(fe_one()) equals `_one_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes the field identity as canonical little-endian one")
expect(fe_to_bytes(fe_one())).to_equal(_one_bytes())
```

</details>

#### squares across the 64-bit boundary without collapsing to zero

- squares across the 64-bit boundary without collapsing to zero
   - Expected: fe_to_bytes(x) equals `_two_pow_64_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("squares across the 64-bit boundary without collapsing to zero")
var x = fe_add(fe_one(), fe_one())
var i: u64 = 0
while i < 6:
    x = fe_sq(x)
    i = i + 1
expect(fe_to_bytes(x)).to_equal(_two_pow_64_bytes())
```

</details>

#### inverts two so two times inverse two is one

- inverts two so two times inverse two is one
   - Expected: fe_to_bytes(fe_mul(two, fe_invert(two))) equals `_one_bytes()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inverts two so two times inverse two is one")
val two = fe_add(fe_one(), fe_one())
expect(fe_to_bytes(fe_mul(two, fe_invert(two)))).to_equal(_one_bytes())
```

</details>

#### adds the Ed25519 identity point without changing the base point

- adds the Ed25519 identity point without changing the base point
   - Expected: ed_point_encode(sum) equals `ed_point_encode(base)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds the Ed25519 identity point without changing the base point")
val base = _ed25519_base_point()
val sum = ed_point_add(ed_point_identity(), base)
expect(ed_point_encode(sum)).to_equal(ed_point_encode(base))
```

</details>

#### scalar-multiplies the base point by one

- scalar-multiplies the base point by one
   - Expected: ed_point_encode(ed_scalar_mul(one, base)) equals `ed_point_encode(base)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar-multiplies the base point by one")
val base = _ed25519_base_point()
val one = _one_bytes()
expect(ed_point_encode(ed_scalar_mul(one, base))).to_equal(ed_point_encode(base))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ed25519_field_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ed25519 field and base-point primitives.
- Ed25519 field and base-point primitives

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

- Canonical SPipe generation for source `d40af3219c379f467bc4f8c147042aa447e9d51b2b063b37ddcd07ce5ff98dd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d40af3219c379f467bc4f8c147042aa447e9d51b2b063b37ddcd07ce5ff98dd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d40af3219c379f467bc4f8c147042aa447e9d51b2b063b37ddcd07ce5ff98dd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/crypto/ed25519_field_ops_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/ed25519_field_ops_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/crypto/ed25519_field_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/ed25519_field_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/ed25519_field_ops_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes the field identity as canonical little-endian one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/ed25519_field_ops_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'squares across the 64-bit boundary without collapsing to zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/ed25519_field_ops_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inverts two so two times inverse two is one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
