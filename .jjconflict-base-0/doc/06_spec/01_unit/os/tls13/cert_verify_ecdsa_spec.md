# Cert Verify Ecdsa Specification

> <details>

<!-- sdn-diagram:id=cert_verify_ecdsa_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cert_verify_ecdsa_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cert_verify_ecdsa_spec -> std
cert_verify_ecdsa_spec -> os
cert_verify_ecdsa_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cert_verify_ecdsa_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cert Verify Ecdsa Specification

## Scenarios

### ECDSA-P256 DER sig decode

#### fixed64_to_der produces a non-empty byte sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign_fixed(_pkcs8(), _test_msg())
val der = _fixed64_to_der(sig)
expect(der.len() > 0).to_equal(true)
```

</details>

#### DER-encoded sig starts with SEQUENCE tag 0x30

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = ecdsa_p256_sign_fixed(_pkcs8(), _test_msg())
val der = _fixed64_to_der(sig)
expect(der[0u64]).to_equal(0x30u8)
```

</details>

#### DER-encoded sig verifies correctly with ecdsa_p256_verify_fixed after round-trip

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sign → DER-encode → decode back to fixed64 → verify
# This tests the DER decoder path that cert_verify uses internally
val msg = _test_msg()
val fixed64 = ecdsa_p256_sign_fixed(_pkcs8(), msg)
val der = _fixed64_to_der(fixed64)
# Decode the DER back to fixed64 via the cert_verify API
# (We test via verify_certificate_verify_msg_scheme which uses the decoder)
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, der)
if val CertVerifyResult.Ok = result:
    expect(fixed64.len()).to_equal(64u64)
    expect(der[0u64]).to_equal(0x30u8)
else:
    fail("DER-encoded ECDSA-P256 signature did not verify after round-trip")
```

</details>

### verify_certificate_verify_msg_scheme ECDSA-P256-SHA-256 (0x0403)

#### verifies a valid ECDSA-P256 CertificateVerify message

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _test_msg()
val der_sig = _sign_msg_der()
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, der_sig)
if val CertVerifyResult.Ok = result:
    expect(_spki().len()).to_equal(91u64)
    expect(der_sig[0u64]).to_equal(0x30u8)
else:
    fail("valid ECDSA-P256 CertificateVerify message was rejected")
```

</details>

#### rejects signature verified under a different public key

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _test_msg()
val der_sig = _sign_msg_der()
val result = verify_certificate_verify_msg_scheme(_other_spki(), 0x0403u16, msg, der_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(_other_spki().len()).to_equal(91u64)
    expect(err_msg).to_equal("CertificateVerify signature invalid (ecdsa_secp256r1_sha256)")
else:
    fail("ECDSA-P256 CertificateVerify unexpectedly accepted a different public key")
```

</details>

#### rejects a DER signature with a flipped byte

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _test_msg()
val der_sig = _sign_msg_der()
# Flip a byte inside the signature content (byte 4 = first byte of r value)
val bad_sig = _flip_byte_at(der_sig, 4u64)
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0403u16, msg, bad_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(bad_sig[0u64]).to_equal(0x30u8)
    expect(err_msg).to_equal("CertificateVerify signature invalid (ecdsa_secp256r1_sha256)")
else:
    fail("ECDSA-P256 CertificateVerify unexpectedly accepted a flipped DER signature byte")
```

</details>

### verify_certificate_verify_msg_scheme unsupported ECDSA schemes

#### sig_scheme 0x0503 (ecdsa_secp384r1_sha384) returns unsupported error

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _test_msg()
val dummy_sig: [u8] = [0x30u8, 0x06u8, 0x02u8, 0x01u8, 0x01u8, 0x02u8, 0x01u8, 0x01u8]
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0503u16, msg, dummy_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(err_msg.contains("P-384")).to_equal(true)
else:
    fail("unsupported ECDSA P-384 signature scheme was accepted")
```

</details>

#### sig_scheme 0x0603 (ecdsa_secp521r1_sha512) returns unsupported error

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _test_msg()
val dummy_sig: [u8] = [0x30u8, 0x06u8, 0x02u8, 0x01u8, 0x01u8, 0x02u8, 0x01u8, 0x01u8]
val result = verify_certificate_verify_msg_scheme(_spki(), 0x0603u16, msg, dummy_sig)
if val CertVerifyResult.Err(err_msg) = result:
    expect(err_msg.contains("P-521")).to_equal(true)
else:
    fail("unsupported ECDSA P-521 signature scheme was accepted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/cert_verify_ecdsa_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
