# Ed25519 Ct Property Specification

> Tests covering Ed25519 constant-time discipline on secret-scalar path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Ct Property Specification

## Scenarios

### Ed25519 constant-time discipline on secret-scalar path

#### derives the same public key when called twice on the same seed (determinism)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### produces identical signatures for identical inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _seed_filled(0xA5.to_u8())
val kp = ed25519_keypair_from_seed(seed)
val pubkey = kp.1
val msg = _msg_deadbeef()
val sig1 = ed25519_sign(seed, pubkey, msg)
val sig2 = ed25519_sign(seed, pubkey, msg)
expect(sig1.len()).to_be(64)
expect(_bytes_equal(a: sig1, b: sig2)).to_be(true)
```

</details>

#### signs+verifies under a low-Hamming-weight seed (seed = 0x00 * 32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _seed_filled(0x00.to_u8())
val kp = ed25519_keypair_from_seed(seed)
val pubkey = kp.1
val msg = _msg_one()
val sig = ed25519_sign(seed, pubkey, msg)
expect(sig.len()).to_be(64)
expect(ed25519_verify(pubkey, msg, sig)).to_be(true)
```

</details>

#### signs+verifies under a high-Hamming-weight seed (seed = 0xFF * 32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = _seed_filled(0xFF.to_u8())
val kp = ed25519_keypair_from_seed(seed)
val pubkey = kp.1
val msg = _msg_one()
val sig = ed25519_sign(seed, pubkey, msg)
expect(sig.len()).to_be(64)
expect(ed25519_verify(pubkey, msg, sig)).to_be(true)
```

</details>

#### structural CT: ed_scalar_mul body contains no `if` branch on a scalar bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `ed_scalar_mul` lives in ed25519_ops.spl, not ed25519.spl. This
# spec used to read the wrong file, so `src.find(hdr)` returned -1
# and the example failed for a reason unrelated to the property it
# claims to test — it could never have gone green, and could never
# have caught a real regression either.
val src = rt_file_read_text("src/os/crypto/ed25519_ops.spl")

# Locate the function header.
val hdr = "fn ed_scalar_mul(scalar: [u8], p: EdPoint) -> EdPoint:"
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
val has_byte_val_branch = (body.find("if ((byte_val")) >= 0
val has_scalar_branch = (body.find("if scalar[")) >= 0
val has_shr_eq_one = (body.find(") & 1) == 1")) >= 0

expect(has_byte_val_branch).to_be(false)
expect(has_scalar_branch).to_be(false)
expect(has_shr_eq_one).to_be(false)

# Positive sanity: the new body MUST call the constant-time helper.
val cselect_idx: i64 = body.find("ed_point_cselect")
expect(cselect_idx >= 0).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/ed25519_ct_property_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ed25519 constant-time discipline on secret-scalar path.
- Ed25519 constant-time discipline on secret-scalar path

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

- Canonical SPipe generation for source `a1aa8b10632e0875c2af40da949bb91c2b2c903f279eaef494ec52001ad6ad71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1aa8b10632e0875c2af40da949bb91c2b2c903f279eaef494ec52001ad6ad71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1aa8b10632e0875c2af40da949bb91c2b2c903f279eaef494ec52001ad6ad71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/crypto/ed25519_ct_property_spec.spl
mirror: doc/06_spec/unit/lib/crypto/ed25519_ct_property_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/ed25519_ct_property_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/ed25519_ct_property_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/ed25519_ct_property_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/lib/crypto/ed25519_ct_property_spec.spl:85:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'derives the same public key when called twice on the same seed (determinism)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/ed25519_ct_property_spec.spl:96:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'produces identical signatures for identical inputs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/ed25519_ct_property_spec.spl:106:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'signs+verifies under a low-Hamming-weight seed (seed = 0x00 * 32)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/lib/crypto/ed25519_ct_property_spec.spl:115:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'signs+verifies under a high-Hamming-weight seed (seed = 0xFF * 32)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
