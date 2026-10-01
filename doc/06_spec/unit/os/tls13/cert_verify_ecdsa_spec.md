# Cert Verify Ecdsa Specification

> Tests covering ECDSA-P256 DER sig decode, verify_certificate_verify_msg_scheme ECDSA-P256-SHA-256 (0x0403), verify_certificate_verify_msg_scheme unsupported ECDSA schemes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cert Verify Ecdsa Specification

## Scenarios

### ECDSA-P256 DER sig decode

#### fixed64_to_der produces a non-empty byte sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fixed64_to_der produces a non-empty byte sequence
   - Expected: der.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fixed64_to_der produces a non-empty byte sequence")
val sig = ecdsa_p256_sign_fixed(_pkcs8(), _test_msg())
val der = _fixed64_to_der(sig)
expect(der.len() > 0).to_equal(true)
```

</details>

#### DER-encoded sig starts with SEQUENCE tag 0x30

- DER-encoded sig starts with SEQUENCE tag 0x30
   - Expected: der[0u64] equals `0x30u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DER-encoded sig starts with SEQUENCE tag 0x30")
val sig = ecdsa_p256_sign_fixed(_pkcs8(), _test_msg())
val der = _fixed64_to_der(sig)
expect(der[0u64]).to_equal(0x30u8)
```

</details>

#### DER-encoded sig verifies correctly with ecdsa_p256_verify_fixed after round-trip

- DER-encoded sig verifies correctly with ecdsa_p256_verify_fixed after round-trip
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DER-encoded sig verifies correctly with ecdsa_p256_verify_fixed after round-trip")
# Sign → DER-encode → decode back to fixed64 → verify
# This tests the DER decoder path that cert_verify uses internally
val msg = _test_msg()
val fixed64 = ecdsa_p256_sign_fixed(_pkcs8(), msg)
val der = _fixed64_to_der(fixed64)
# Decode the DER back to fixed64 via the cert_verify API
# (We test via verify_certificate_verify_msg_scheme which uses the decoder)
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, der)
if val CertVerifyResult.Ok = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### verify_certificate_verify_msg_scheme ECDSA-P256-SHA-256 (0x0403)

#### verifies a valid ECDSA-P256 CertificateVerify message

- verifies a valid ECDSA-P256 CertificateVerify message
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies a valid ECDSA-P256 CertificateVerify message")
val msg = _test_msg()
val der_sig = _sign_msg_der()
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, der_sig)
if val CertVerifyResult.Ok = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects signature verified under a different public key

- rejects signature verified under a different public key
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects signature verified under a different public key")
val msg = _test_msg()
val der_sig = _sign_msg_der()
val result = verify_certificate_verify_msg_scheme(_other_spki(), 0x0403u16, msg, der_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects a DER signature with a flipped byte

- rejects a DER signature with a flipped byte
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a DER signature with a flipped byte")
val msg = _test_msg()
val der_sig = _sign_msg_der()
# Flip a byte inside the signature content (byte 4 = first byte of r value)
val bad_sig = _flip_byte_at(der_sig, 4u64)
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### verify_certificate_verify_msg_scheme unsupported ECDSA schemes

#### sig_scheme 0x0503 (ecdsa_secp384r1_sha384) returns unsupported error

- sig_scheme 0x0503 (ecdsa_secp384r1_sha384) returns unsupported error
   - Expected: err_msg contains `P-384`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sig_scheme 0x0503 (ecdsa_secp384r1_sha384) returns unsupported error")
val msg = _test_msg()
val dummy_sig: [u8] = [0x30u8, 0x06u8, 0x02u8, 0x01u8, 0x01u8, 0x02u8, 0x01u8, 0x01u8]
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0503u16, msg, dummy_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(err_msg.contains("P-384")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### sig_scheme 0x0603 (ecdsa_secp521r1_sha512) returns unsupported error

- sig_scheme 0x0603 (ecdsa_secp521r1_sha512) returns unsupported error
   - Expected: err_msg contains `P-521`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sig_scheme 0x0603 (ecdsa_secp521r1_sha512) returns unsupported error")
val msg = _test_msg()
val dummy_sig: [u8] = [0x30u8, 0x06u8, 0x02u8, 0x01u8, 0x01u8, 0x02u8, 0x01u8, 0x01u8]
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0603u16, msg, dummy_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(err_msg.contains("P-521")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/cert_verify_ecdsa_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ECDSA-P256 DER sig decode, verify_certificate_verify_msg_scheme ECDSA-P256-SHA-256 (0x0403), verify_certificate_verify_msg_scheme unsupported ECDSA schemes.
- ECDSA-P256 DER sig decode
- verify_certificate_verify_msg_scheme ECDSA-P256-SHA-256 (0x0403)
- verify_certificate_verify_msg_scheme unsupported ECDSA schemes

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

- Canonical SPipe generation for source `9dea232fbca8c48d8bfcdd25a5d827451a5b19765a4a055b7a868c0409e88393`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dea232fbca8c48d8bfcdd25a5d827451a5b19765a4a055b7a868c0409e88393`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dea232fbca8c48d8bfcdd25a5d827451a5b19765a4a055b7a868c0409e88393`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/cert_verify_ecdsa_spec.spl
mirror: doc/06_spec/unit/os/tls13/cert_verify_ecdsa_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/cert_verify_ecdsa_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/cert_verify_ecdsa_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/cert_verify_ecdsa_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fixed64_to_der produces a non-empty byte sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/cert_verify_ecdsa_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DER-encoded sig starts with SEQUENCE tag 0x30' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/cert_verify_ecdsa_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DER-encoded sig verifies correctly with ecdsa_p256_verify_fixed after round-trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
