# Rsa Pss Sha256 Roundtrip Slow Specification

> <details>

<!-- sdn-diagram:id=rsa_pss_sha256_roundtrip_slow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_pss_sha256_roundtrip_slow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_pss_sha256_roundtrip_slow_spec -> std
rsa_pss_sha256_roundtrip_slow_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_pss_sha256_roundtrip_slow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pss Sha256 Roundtrip Slow Specification

## Scenarios

### RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow)

#### produces 256-byte signature for RSA-2048 key (sLen=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(sig.len().to_i64()).to_equal(256)
```

</details>

#### verifies signature with sLen=0 (deterministic encoding)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(rsa_pss_sha256_verify_with_slen(_spki(), _msg_hello(), sig, 0)).to_equal(true)
```

</details>

#### verifies signature with sLen=32 (default hLen)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), sig)).to_equal(true)
```

</details>

#### deterministic PSS (sLen=0) is byte-reproducible

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
val s2 = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _empty_salt())
expect(s1.len().to_i64()).to_equal(s2.len().to_i64())
var i: u64 = 0
var ok: bool = true
while i < s1.len():
    if s1[i] != s2[i]:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### rejects signature with last byte flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
val tampered = _flip_byte(sig, sig.len() - 1u64)
expect(rsa_pss_sha256_verify(_spki(), _msg_hello(), tampered)).to_equal(false)
```

</details>

#### rejects valid signature against different message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = rsa_pss_sha256_sign(_pkcs8(), _msg_hello(), _fixed_salt_32())
expect(rsa_pss_sha256_verify(_spki(), _msg_different(), sig)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RSA-PSS-SHA-256 sign + verify round-trip (RSA-2048, slow)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
