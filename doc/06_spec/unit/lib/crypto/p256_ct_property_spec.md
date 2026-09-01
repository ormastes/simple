# P256 Ct Property Specification

> Tests covering P-256 constant-time discipline on secret-scalar path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Ct Property Specification

## Scenarios

### P-256 constant-time discipline on secret-scalar path

#### derives the same public key when called twice on the same scalar (determinism)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### two scalars differing in one bit produce distinct public keys (k=1 vs k=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = _scalar_one()
val s2 = _scalar_two()
val key1 = p256_keypair_pub(s1)
val key2 = p256_keypair_pub(s2)
expect(key1.len()).to_be(65)
expect(key2.len()).to_be(65)
expect(_bytes_equal(a: key1, b: key2)).to_be(false)
```

</details>

#### low-Hamming-weight scalar (0x00..0x01) produces a valid 65-byte SEC1 point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = _scalar_one()
val key = p256_keypair_pub(scalar)
expect(key.len()).to_be(65)
expect(key[0u64]).to_equal(0x04.to_u8())
```

</details>

#### high-Hamming-weight scalar (0xFF * 32) produces a valid 65-byte SEC1 point

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar = _scalar_filled(0xFF.to_u8())
val key = p256_keypair_pub(scalar)
expect(key.len()).to_be(65)
expect(key[0u64]).to_equal(0x04.to_u8())
```

</details>

#### structural CT: _scalar_mul_affine body contains no `if` branch on a scalar bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/os/crypto/ecdh_p256.spl")

# Locate the function header.
val hdr = "fn _scalar_mul_affine(scalar: [u8], ax: FeP256, ay: FeP256) -> JacP256:"
val start_opt = src.find(hdr)
val start: i64 = start_opt ?? (-1).to_i64()
expect(start >= 0).to_be(true)

# The body ends at the next top-level `\nfn ` after the header.
val after_hdr: u64 = (start.to_u64()) + hdr.len()
val rest = src.substring(after_hdr, src.len())
val next_fn_opt = rest.find("\nfn ")
var body_end: u64 = src.len()
val nfo: i64 = next_fn_opt ?? (-1).to_i64()
if nfo >= 0:
    body_end = after_hdr + nfo.to_u64()

val body = src.substring(after_hdr, body_end)

# OLD branchful form fingerprints. None of these may survive.
val has_byte_mask_branch = (body.find("if (byte & mask)")) >= 0
val has_byte_amp_branch = (body.find("if (byte &")) >= 0
val has_scalar_idx_branch = (body.find("if scalar[")) >= 0
val has_neq_zero = (body.find("!= 0u8")) >= 0

expect(has_byte_mask_branch).to_be(false)
expect(has_byte_amp_branch).to_be(false)
expect(has_scalar_idx_branch).to_be(false)
expect(has_neq_zero).to_be(false)

# Positive sanity: the new body MUST call the constant-time helper.
val cselect_idx: i64 = body.find("p256_point_cselect")
expect(cselect_idx >= 0).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/p256_ct_property_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering P-256 constant-time discipline on secret-scalar path.
- P-256 constant-time discipline on secret-scalar path

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

- Canonical SPipe generation for source `9ad37f31e4be8e4bdf3aeb5a677cbeb531f308db9b8abbd3ad01188c99e73ac7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ad37f31e4be8e4bdf3aeb5a677cbeb531f308db9b8abbd3ad01188c99e73ac7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ad37f31e4be8e4bdf3aeb5a677cbeb531f308db9b8abbd3ad01188c99e73ac7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/crypto/p256_ct_property_spec.spl
mirror: doc/06_spec/unit/lib/crypto/p256_ct_property_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/p256_ct_property_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/p256_ct_property_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/p256_ct_property_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/crypto/p256_ct_property_spec.spl:94:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'derives the same public key when called twice on the same scalar (determinism)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/p256_ct_property_spec.spl:103:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'two scalars differing in one bit produce distinct public keys (k=1 vs k=2)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/p256_ct_property_spec.spl:112:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'low-Hamming-weight scalar (0x00..0x01) produces a valid 65-byte SEC1 point' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/p256_ct_property_spec.spl:118:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'high-Hamming-weight scalar (0xFF * 32) produces a valid 65-byte SEC1 point' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
