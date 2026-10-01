# Ed25519 Strict Verify Specification

> Tests covering pure-Simple Ed25519 strict verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ed25519 Strict Verify Specification

## Scenarios

### pure-Simple Ed25519 strict verification

#### derives the RFC 8032 SHA(abc) public key exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives the RFC 8032 SHA(abc) public key exactly
   - Expected: keypair.1 equals `PUB_SHA_ABC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the RFC 8032 SHA(abc) public key exactly")
val keypair = pure_ed25519_keypair_from_seed(SEED_SHA_ABC)
expect(keypair.1).to_equal(PUB_SHA_ABC)
```

</details>

#### accepts the RFC 8032 SHA(abc) signature

- accepts the RFC 8032 SHA(abc) signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the RFC 8032 SHA(abc) signature")
expect(pure_ed25519_verify(PUB_SHA_ABC, MSG_SHA_ABC, SIG_SHA_ABC)).to_be(true)
```

</details>

#### signs the RFC 8032 SHA(abc) vector byte-for-byte

- signs the RFC 8032 SHA(abc) vector byte-for-byte
   - Expected: signature equals `SIG_SHA_ABC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signs the RFC 8032 SHA(abc) vector byte-for-byte")
val signature = pure_ed25519_sign(SEED_SHA_ABC, PUB_SHA_ABC, MSG_SHA_ABC)
expect(signature).to_equal(SIG_SHA_ABC)
```

</details>

#### rejects S equal to the group order L

- rejects S equal to the group order L


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects S equal to the group order L")
expect(pure_ed25519_verify(PUB_SHA_ABC, MSG_SHA_ABC, _signature_with_s_l())).to_be(false)
```

</details>

#### rejects the identity-key universal-forgery shape

- rejects the identity-key universal-forgery shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the identity-key universal-forgery shape")
expect(pure_ed25519_verify(_identity_encoding(), [], _identity_forgery())).to_be(false)
```

</details>

#### rejects an order-two public key

- rejects an order-two public key


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an order-two public key")
expect(pure_ed25519_verify(_order_two_encoding(), MSG_SHA_ABC, SIG_SHA_ABC)).to_be(false)
```

</details>

#### rejects y equal to non-canonical field modulus p

- rejects y equal to non-canonical field modulus p


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects y equal to non-canonical field modulus p")
expect(pure_ed25519_verify(_noncanonical_p_encoding(), MSG_SHA_ABC, SIG_SHA_ABC)).to_be(false)
```

</details>

#### rejects a y coordinate whose curve equation has no square root

- rejects a y coordinate whose curve equation has no square root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a y coordinate whose curve equation has no square root")
expect(pure_ed25519_verify(_invalid_y_two_encoding(), MSG_SHA_ABC, SIG_SHA_ABC)).to_be(false)
```

</details>

#### rejects the forbidden negative encoding of x zero

- rejects the forbidden negative encoding of x zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the forbidden negative encoding of x zero")
expect(pure_ed25519_verify(_negative_zero_encoding(), MSG_SHA_ABC, SIG_SHA_ABC)).to_be(false)
```

</details>

#### rejects an identity R point

- rejects an identity R point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an identity R point")
val bad_sig = _signature_with_r(_identity_encoding())
expect(pure_ed25519_verify(PUB_SHA_ABC, MSG_SHA_ABC, bad_sig)).to_be(false)
```

</details>

#### rejects a non-canonical R point

- rejects a non-canonical R point


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-canonical R point")
val bad_sig = _signature_with_r(_noncanonical_p_encoding())
expect(pure_ed25519_verify(PUB_SHA_ABC, MSG_SHA_ABC, bad_sig)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/ed25519_strict_verify_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple Ed25519 strict verification.
- pure-Simple Ed25519 strict verification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `c4ff030b39ce8aeef4b5823cda7ea452e5c0db2219b6c09678bfa3be27980c8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4ff030b39ce8aeef4b5823cda7ea452e5c0db2219b6c09678bfa3be27980c8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4ff030b39ce8aeef4b5823cda7ea452e5c0db2219b6c09678bfa3be27980c8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/crypto/ed25519_strict_verify_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/ed25519_strict_verify_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/ed25519_strict_verify_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/ed25519_strict_verify_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/ed25519_strict_verify_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the RFC 8032 SHA(abc) public key exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/ed25519_strict_verify_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the RFC 8032 SHA(abc) signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/ed25519_strict_verify_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signs the RFC 8032 SHA(abc) vector byte-for-byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
