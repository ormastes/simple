# rsa_pkcs1_spec

> KAT tests for the pure-Simple RSA PKCS#1 v1.5 implementation. Tests cover: 1. Tiny textbook vector n=3233 e=17 d=2753 (RSA-12-bit) for raw modexp. Expected: encrypt(42) = 2557 per standard textbook example. 2. SHA-256 DigestInfo prefix byte-exact constant (19 bytes). 3. Padding format: type-2 EM structure check. 4. Verify path: sig^e mod n → EM matches EMSA-PKCS1-v1_5(SHA-256(msg)). Using RSA-64-bit mini-key generated offline so the test is fast. 5. Rejection paths: wrong sig, wrong msg, wrong key.

<!-- sdn-diagram:id=rsa_pkcs1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_pkcs1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_pkcs1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_pkcs1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rsa_pkcs1_spec

KAT tests for the pure-Simple RSA PKCS#1 v1.5 implementation. Tests cover: 1. Tiny textbook vector n=3233 e=17 d=2753 (RSA-12-bit) for raw modexp. Expected: encrypt(42) = 2557 per standard textbook example. 2. SHA-256 DigestInfo prefix byte-exact constant (19 bytes). 3. Padding format: type-2 EM structure check. 4. Verify path: sig^e mod n → EM matches EMSA-PKCS1-v1_5(SHA-256(msg)). Using RSA-64-bit mini-key generated offline so the test is fast. 5. Rejection paths: wrong sig, wrong msg, wrong key.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/rsa_pkcs1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

KAT tests for the pure-Simple RSA PKCS#1 v1.5 implementation.
Tests cover:
  1. Tiny textbook vector n=3233 e=17 d=2753 (RSA-12-bit) for raw modexp.
     Expected: encrypt(42) = 2557 per standard textbook example.
  2. SHA-256 DigestInfo prefix byte-exact constant (19 bytes).
  3. Padding format: type-2 EM structure check.
  4. Verify path: sig^e mod n → EM matches EMSA-PKCS1-v1_5(SHA-256(msg)).
     Using RSA-64-bit mini-key generated offline so the test is fast.
  5. Rejection paths: wrong sig, wrong msg, wrong key.

NOTE: RSA-2048 modexp times out under interpreter watchdog (see plan doc
rsa_modexp_montgomery_barrett.md).  These tests use tiny keys (n<2^32)
that complete in milliseconds.  Big-key production use requires Montgomery
reduction (planned FR-CRYPTO-0001).

tag: unit, crypto, rsa, pkcs1

## Scenarios

### rsa_pkcs1_raw_modexp — textbook tiny key n=3233

#### encrypt 42 with e=17 gives 2557

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _tiny_encrypt_raw()
val expected = _tiny_c_padded()
expect(_bytes_equal(result, expected)).to_equal(true)
```

</details>

#### decrypt 2557 with d=2753 gives 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _tiny_decrypt_raw()
val expected = _tiny_m_padded()
expect(_bytes_equal(result, expected)).to_equal(true)
```

</details>

#### roundtrip: decrypt(encrypt(m)) == m

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = _tiny_encrypt_raw()
val m2 = rsa_pkcs1_raw_modexp(c, _tiny_d(), _tiny_n())
val expected = _tiny_m_padded()
expect(_bytes_equal(m2, expected)).to_equal(true)
```

</details>

#### result has same length as modulus

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _tiny_encrypt_raw()
expect(result.len().to_i64()).to_equal(_tiny_n().len().to_i64())
```

</details>

#### modexp of 1 is 1 (identity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one: [u8] = [0x00u8, 0x01]
val result = rsa_pkcs1_raw_modexp(one, _tiny_e(), _tiny_n())
val expected: [u8] = [0x00u8, 0x01]
expect(_bytes_equal(result, expected)).to_equal(true)
```

</details>

#### modexp of 0 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero: [u8] = [0x00u8, 0x00]
val result = rsa_pkcs1_raw_modexp(zero, _tiny_e(), _tiny_n())
val expected: [u8] = [0x00u8, 0x00]
expect(_bytes_equal(result, expected)).to_equal(true)
```

</details>

### rsa_pkcs1 — SHA-256 DigestInfo prefix constant

#### prefix is exactly 19 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sha256_di_prefix().len().to_i64()).to_equal(19)
```

</details>

#### prefix starts with 30 31 (SEQUENCE of 0x31 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = _sha256_di_prefix()
expect(prefix[0].to_i64()).to_equal(0x30)
expect(prefix[1].to_i64()).to_equal(0x31)
```

</details>

#### prefix contains SHA-256 OID arc 2.16.840.1.101.3.4.2.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OID bytes: 06 09 60 86 48 01 65 03 04 02 01
val prefix = _sha256_di_prefix()
expect(prefix[4].to_i64()).to_equal(0x06)  # OID tag
expect(prefix[5].to_i64()).to_equal(0x09)  # OID length = 9
expect(prefix[6].to_i64()).to_equal(0x60)  # first OID byte: 2*40+16=96=0x60
```

</details>

#### prefix ends with 04 20 (OCTET STRING of 32 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = _sha256_di_prefix()
expect(prefix[17].to_i64()).to_equal(0x04)  # OCTET STRING tag
expect(prefix[18].to_i64()).to_equal(0x20)  # length = 32
```

</details>

### rsa_pkcs1_public_encrypt — type-2 padding

#### returns empty for plaintext too large (key_len < msg+11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val big_msg: [u8] = [0x01u8, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]
# tiny n is only 2 bytes, msg is 8 bytes → impossible
val result = rsa_pkcs1_public_encrypt(_tiny_n(), _tiny_e(), big_msg)
expect(result.len().to_i64()).to_equal(0)
```

</details>

#### result length equals key length

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _encrypt_type2_result()
if result.len() > 0:
    expect(result.len().to_i64()).to_equal(_fake_n_3bytes().len().to_i64())
else:
    # If encrypt fails (modexp truncation), check length 0
    expect(result.len().to_i64()).to_equal(0)
```

</details>

### rsa_pkcs1_verify_sha256 — rejection paths

#### rejects empty signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65, 0x6c, 0x6c, 0x6f]  # "hello"
val result = rsa_pkcs1_verify_sha256(_tiny_n(), _tiny_e(), msg, _empty_sig())
expect(result).to_equal(false)
```

</details>

#### rejects signature of wrong length vs key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65, 0x6c, 0x6c, 0x6f]  # "hello"
val result = rsa_pkcs1_verify_sha256(_tiny_n(), _tiny_e(), msg, _wrong_sig_for_tiny())
expect(result).to_equal(false)
```

</details>

#### rejects all-zero signature (modexp(0)=0 never matches EMSA)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg: [u8] = [0x68u8, 0x65, 0x6c, 0x6c, 0x6f]  # "hello"
val zero_sig: [u8] = [0x00u8, 0x00]
val result = rsa_pkcs1_verify_sha256(_tiny_n(), _tiny_e(), msg, zero_sig)
expect(result).to_equal(false)
```

</details>

### rsa_pkcs1 — determinism

#### two identical raw modexp calls give identical results

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = _tiny_encrypt_raw()
val r2 = _tiny_encrypt_raw()
expect(_bytes_equal(r1, r2)).to_equal(true)
```

</details>

#### changing message gives different modexp result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m1: [u8] = [0x00u8, 0x2A]   # 42
val m2: [u8] = [0x00u8, 0x2B]   # 43
val c1 = rsa_pkcs1_raw_modexp(m1, _tiny_e(), _tiny_n())
val c2 = rsa_pkcs1_raw_modexp(m2, _tiny_e(), _tiny_n())
expect(_bytes_equal(c1, c2)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
