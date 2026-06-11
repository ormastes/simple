# Chacha20 Specification

> <details>

<!-- sdn-diagram:id=chacha20_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Specification

## Scenarios

### ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector

#### produces correct a after quarter-round

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _qr_test_vector()
expect(result[0]).to_equal(0xea2a92f4u32)
```

</details>

#### produces correct b after quarter-round

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _qr_test_vector()
expect(result[1]).to_equal(0xcb1cf8ceu32)
```

</details>

#### produces correct c after quarter-round

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _qr_test_vector()
expect(result[2]).to_equal(0x4581472eu32)
```

</details>

#### produces correct d after quarter-round

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _qr_test_vector()
expect(result[3]).to_equal(0x5881c4bbu32)
```

</details>

### ChaCha20 RFC 7539 §2.3.2 — block function test vector

#### block output is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = chacha20_block(_key_words_2_3_2(), 1u32, _nonce_words_2_3_2())
expect(block.len()).to_equal(16u64)
```

</details>

#### block bytes match RFC 7539 §2.3.2 exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = chacha20_block(_key_words_2_3_2(), 1u32, _nonce_words_2_3_2())
val got = _block_to_bytes(block)
expect(_bytes_eq(got, _expected_block_2_3_2())).to_equal(true)
```

</details>

### ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector

#### ciphertext length matches plaintext length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(ct.len()).to_equal(114u64)
```

</details>

#### ciphertext matches RFC 7539 §2.4.2 expected bytes exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct, _expected_ct_2_4_2())).to_equal(true)
```

</details>

#### decryption recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val pt2 = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), ct)
expect(_bytes_eq(pt2, _pt_2_4_2())).to_equal(true)
```

</details>

### ChaCha20 — negative tests (wrong key / nonce / counter change output)

#### wrong key produces different ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
# Flip bit 0 of key byte 0
val bad_key = [0x01u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
               0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8, 0x0fu8,
               0x10u8, 0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8,
               0x18u8, 0x19u8, 0x1au8, 0x1bu8, 0x1cu8, 0x1du8, 0x1eu8, 0x1fu8]
val ct_bad = chacha20_encrypt(bad_key, 1u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

#### wrong nonce produces different ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val bad_nonce = [0x01u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x4au8,
                 0x00u8, 0x00u8, 0x00u8, 0x00u8]
val ct_bad = chacha20_encrypt(_key_2_4_2(), 1u32, bad_nonce, _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

#### wrong counter produces different ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct_good = chacha20_encrypt(_key_2_4_2(), 1u32, _nonce_2_4_2(), _pt_2_4_2())
val ct_bad  = chacha20_encrypt(_key_2_4_2(), 2u32, _nonce_2_4_2(), _pt_2_4_2())
expect(_bytes_eq(ct_good, ct_bad)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/chacha20_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20 RFC 7539 §2.1.1 — quarter-round test vector
- ChaCha20 RFC 7539 §2.3.2 — block function test vector
- ChaCha20 RFC 7539 §2.4.2 — stream encryption test vector
- ChaCha20 — negative tests (wrong key / nonce / counter change output)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
