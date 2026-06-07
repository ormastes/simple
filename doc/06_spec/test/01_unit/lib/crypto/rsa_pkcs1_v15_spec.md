# Rsa Pkcs1 V15 Specification

> <details>

<!-- sdn-diagram:id=rsa_pkcs1_v15_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_pkcs1_v15_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_pkcs1_v15_spec -> std
rsa_pkcs1_v15_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_pkcs1_v15_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pkcs1 V15 Specification

## Scenarios

### RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip

#### signs empty message and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_empty(), _sig_empty())).to_equal(true)
```

</details>

#### signature is non-empty for empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sig_valid(_sig_empty())).to_equal(true)
```

</details>

#### signature is 256 bytes for RSA-2048 key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modulus is 2048 bits = 256 bytes; signature must match modulus length
expect(_sig_hello().len().to_i64()).to_equal(256)
```

</details>

#### signs 'Hello' and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_hello(), _sig_hello())).to_equal(true)
```

</details>

#### signs 32-byte message and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_32bytes(), _sig_32bytes())).to_equal(true)
```

</details>

#### signs 256-byte message and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_256bytes(), _sig_256bytes())).to_equal(true)
```

</details>

#### signs 1024-byte message and verifies

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_1024bytes(), _sig_1024bytes())).to_equal(true)
```

</details>

#### rejects a signature with last byte flipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_sha256_verify(_spki(), _msg_hello(), _corrupted_sig_hello())).to_equal(false)
```

</details>

#### rejects signature when message differs (Hello vs hello)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid signature for 'Hello' must not verify against 'hello'
expect(rsa_sha256_verify(_spki(), _different_msg_hello(), _sig_hello())).to_equal(false)
```

</details>

#### rejects empty signature against valid message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_sig: [u8] = []
expect(rsa_sha256_verify(_spki(), _msg_hello(), empty_sig)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/rsa_pkcs1_v15_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RSA-SHA-256 PKCS#1 v1.5 pure-Simple round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
