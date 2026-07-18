# Chacha20 Poly1305 Specification

> <details>

<!-- sdn-diagram:id=chacha20_poly1305_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_poly1305_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_poly1305_spec -> std
chacha20_poly1305_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_poly1305_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Specification

## Scenarios

### ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT

#### encrypt produces correct total output length (114 ciphertext + 16 tag = 130 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
expect(out.len()).to_equal(130)
```

</details>

#### encrypt produces correct ciphertext bytes (first 16)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 0, 16)
val exp = _slice(_expected_ciphertext(), 0, 16)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 16-32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 16, 32)
val exp = _slice(_expected_ciphertext(), 16, 32)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 32-64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 32, 64)
val exp = _slice(_expected_ciphertext(), 32, 64)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct ciphertext bytes (bytes 64-114)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got = _slice(out, 64, 114)
val exp = _slice(_expected_ciphertext(), 64, 114)
expect(got).to_equal(exp)
```

</details>

#### encrypt produces correct Poly1305 tag (last 16 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = chacha20_poly1305_encrypt(_key(), _nonce(), _plaintext(), _aad())
val got_tag = _slice(out, 114, 130)
expect(got_tag).to_equal(_expected_tag())
```

</details>

#### decrypt with correct tag succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), _expected_tag())
expect(_decrypt_ok(res)).to_equal(true)
```

</details>

#### decrypt recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), _expected_tag())
expect(_decrypt_payload(res)).to_equal(_plaintext())
```

</details>

#### decrypt with wrong tag fails authentication

- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
- bad tag push
   - Expected: _decrypt_ok(res) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad_tag: [u8] = []
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
bad_tag.push(0x00)
val res = chacha20_poly1305_decrypt(_key(), _nonce(), _expected_ciphertext(), _aad(), bad_tag)
expect(_decrypt_ok(res)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/chacha20_poly1305_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20-Poly1305 RFC 8439 §2.8.2 AEAD KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
