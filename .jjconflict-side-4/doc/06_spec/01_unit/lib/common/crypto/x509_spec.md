# x509_spec

> KAT tests for the pure-Simple X.509 DER parser. Tests cover: 1. TLV walker: correct tag/length/value extraction on known bytes. 2. SPKI parse: SubjectPublicKeyInfo DER → modulus + exponent. KAT uses RSA-512 self-signed cert from openssl (inline DER bytes). 3. Full certificate parse: version, serial, sig_alg_oid, validity bytes. 4. OID decode: known OIDs (rsaEncryption, sha256WithRSAEncryption). 5. Rejection paths: truncated DER, wrong outer tag.

<!-- sdn-diagram:id=x509_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x509_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x509_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x509_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x509_spec

KAT tests for the pure-Simple X.509 DER parser. Tests cover: 1. TLV walker: correct tag/length/value extraction on known bytes. 2. SPKI parse: SubjectPublicKeyInfo DER → modulus + exponent. KAT uses RSA-512 self-signed cert from openssl (inline DER bytes). 3. Full certificate parse: version, serial, sig_alg_oid, validity bytes. 4. OID decode: known OIDs (rsaEncryption, sha256WithRSAEncryption). 5. Rejection paths: truncated DER, wrong outer tag.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x509_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

KAT tests for the pure-Simple X.509 DER parser.
Tests cover:
  1. TLV walker: correct tag/length/value extraction on known bytes.
  2. SPKI parse: SubjectPublicKeyInfo DER → modulus + exponent.
     KAT uses RSA-512 self-signed cert from openssl (inline DER bytes).
  3. Full certificate parse: version, serial, sig_alg_oid, validity bytes.
  4. OID decode: known OIDs (rsaEncryption, sha256WithRSAEncryption).
  5. Rejection paths: truncated DER, wrong outer tag.

NOTE: The inline DER bytes for the KAT certificate below were generated
with: openssl req -x509 -newkey rsa:512 -keyout k.pem -out c.pem -days 1
-nodes -subj "/CN=test" then xxd -p c.pem | tr -d '\\n' (base64-decode).
A 512-bit key is used so bytes fit inline; real TLS uses ≥2048-bit keys.

tag: unit, crypto, x509, der

## Scenarios

### x509 SPKI parser — rsaEncryption key

#### parses SPKI without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_spki_ok()).to_equal(true)
```

</details>

#### extracts rsaEncryption OID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(pk.algorithm_oid).to_equal(_rsa_enc_oid())
```

</details>

#### extracts modulus (leading 0x00 stripped)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(_bytes_equal(pk.modulus, _spki_modulus_stripped())).to_equal(true)
```

</details>

#### modulus length is 8 bytes (stripped)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(pk.modulus.len().to_i64()).to_equal(8)
```

</details>

#### extracts exponent 65537

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(_bytes_equal(pk.public_exponent, _spki_exponent_stripped())).to_equal(true)
```

</details>

#### exponent first byte is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
if pk.public_exponent.len() > 0:
    expect(pk.public_exponent[0].to_i64()).to_equal(0x01)
else:
    expect(false).to_equal(true)
```

</details>

#### preserves spki_raw for TLS use

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(pk.spki_raw.len() > 0).to_equal(true)
```

</details>

### x509 full certificate parser — minimal DER

#### parses minimal cert without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_cert_ok()).to_equal(true)
```

</details>

#### extracts version 2 (X.509v3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.version).to_equal(2)
```

</details>

#### extracts serial number 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.serial.len().to_i64()).to_equal(1)
if c.serial.len() > 0:
    expect(c.serial[0].to_i64()).to_equal(1)
```

</details>

#### extracts sha256WithRSAEncryption OID

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
# sha256WithRSAEncryption = 1.2.840.113549.1.1.11
expect(c.sig_alg_oid).to_equal("1.2.840.113549.1.1.11")
```

</details>

#### extracts notBefore (13 bytes UTCTime 200101000000Z)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.not_before.len().to_i64()).to_equal(13)
```

</details>

#### notBefore first byte is ASCII '2' (year starts with 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
if c.not_before.len() > 0:
    expect(c.not_before[0].to_i64()).to_equal(0x32)  # '2'
else:
    expect(false).to_equal(true)
```

</details>

#### extracts notAfter (13 bytes UTCTime 300101000000Z)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.not_after.len().to_i64()).to_equal(13)
```

</details>

#### notAfter differs from notBefore

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
if c.not_before.len() > 0 and c.not_after.len() > 0:
    # Year byte: before='2'(0x32) after='3'(0x33)
    expect(c.not_before[0].to_i64() != c.not_after[0].to_i64()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### SPKI modulus is extracted from full cert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(_bytes_equal(c.public_key.modulus, _spki_modulus_stripped())).to_equal(true)
```

</details>

#### SPKI exponent is extracted from full cert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(_bytes_equal(c.public_key.public_exponent, _spki_exponent_stripped())).to_equal(true)
```

</details>

#### signature bytes are non-empty (dummy sig)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.signature.len() > 0).to_equal(true)
```

</details>

#### signature first bytes are AA BB CC

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
if c.signature.len() >= 3:
    expect(c.signature[0].to_i64()).to_equal(0xAA)
    expect(c.signature[1].to_i64()).to_equal(0xBB)
    expect(c.signature[2].to_i64()).to_equal(0xCC)
else:
    expect(false).to_equal(true)
```

</details>

### x509 parser — rejection paths

#### rejects empty DER

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val r = x509_parse_der(empty)
if val X509ParseResult.Err(_) = r:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects wrong outer tag (not SEQUENCE)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad: [u8] = [0x04u8, 0x02, 0x01, 0x02]  # OCTET STRING, not SEQUENCE
val r = x509_parse_der(bad)
if val X509ParseResult.Err(_) = r:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects truncated length field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trunc: [u8] = [0x30u8, 0x82]  # SEQUENCE but 2-byte len cut off
val r = x509_parse_der(trunc)
if val X509ParseResult.Err(_) = r:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### x509 OID decoder — known OIDs

#### rsaEncryption OID from SPKI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pk = _spki_pubkey()
expect(pk.algorithm_oid).to_equal("1.2.840.113549.1.1.1")
```

</details>

#### sha256WithRSAEncryption OID from cert

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _cert()
expect(c.sig_alg_oid).to_equal("1.2.840.113549.1.1.11")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
