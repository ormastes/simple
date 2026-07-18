# Chacha20 Simd Parity Specification

> <details>

<!-- sdn-diagram:id=chacha20_simd_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_simd_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_simd_parity_spec -> std
chacha20_simd_parity_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_simd_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Simd Parity Specification

## Scenarios

### ChaCha20 SIMD vs scalar parity

#### RFC 8439 §2.4.2 SIMD path matches scalar on the 114-byte sunscreen vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct_scalar = chacha20_encrypt(key, 1u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### RFC 8439 §2.4.2 SIMD ciphertext matches the published canonical bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Spot-check the first 4 bytes of ciphertext as published in RFC 8439:
# 0x6e, 0x2e, 0x35, 0x9a (matches the existing scalar KAT in
# test/system/os_crypto_ref_primitives_spec.spl). The SIMD path is a
# tail-only path here (114 < 256), so this verifies the scalar branch
# used inside chacha20_encrypt_simd is byte-exact too.
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _sunscreen_pt()
val ct = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(ct.len()).to_equal(114u64)
expect(ct[0]).to_equal(0x6eu8)
expect(ct[1]).to_equal(0x2eu8)
expect(ct[2]).to_equal(0x35u8)
expect(ct[3]).to_equal(0x9au8)
```

</details>

#### 256-byte aligned payload (one full SIMD chunk, no tail) matches scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _aligned256_pt()
val ct_scalar = chacha20_encrypt(key, 1u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 1u32, nonce, pt)
expect(ct_simd.len()).to_equal(256u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### 600-byte unaligned payload (2 SIMD chunks + 88-byte tail) matches scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _long_pt()
val ct_scalar = chacha20_encrypt(key, 0u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 0u32, nonce, pt)
expect(ct_simd.len()).to_equal(600u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### 1024-byte payload (4 SIMD chunks, no tail) matches scalar with non-zero counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _kib_pt()
val ct_scalar = chacha20_encrypt(key, 7u32, nonce, pt)
val ct_simd = chacha20_encrypt_simd(key, 7u32, nonce, pt)
expect(ct_simd.len()).to_equal(1024u64)
expect(_bytes_eq(ct_scalar, ct_simd)).to_equal(true)
```

</details>

#### SIMD round-trip recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _rfc7539_key()
val nonce = _rfc7539_nonce()
val pt = _long_pt()
val ct = chacha20_encrypt_simd(key, 1u32, nonce, pt)
val recovered = chacha20_encrypt_simd(key, 1u32, nonce, ct)
expect(_bytes_eq(recovered, pt)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/chacha20_simd_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20 SIMD vs scalar parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
