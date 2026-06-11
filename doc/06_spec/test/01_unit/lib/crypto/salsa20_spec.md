# Salsa20 Specification

> <details>

<!-- sdn-diagram:id=salsa20_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=salsa20_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

salsa20_spec -> std
salsa20_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=salsa20_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Salsa20 Specification

## Scenarios

### Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0)

#### block output is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_20_block(_make_key_0x80(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(out.len()).to_equal(64u64)
```

</details>

#### block output matches DJB spec byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_20_block(_make_key_0x80(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set1_v0()))
```

</details>

### Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0)

#### block output is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_0x80(), 0u32, 0u32)
expect(out.len()).to_equal(64u64)
```

</details>

#### block output matches DJB spec byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_0x80(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set2_v0()))
```

</details>

### Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce)

#### block output matches DJB spec byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set0_v0()))
```

</details>

### Salsa20/20 XOR — round-trip and length

#### output length equals plaintext length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8]
val ct = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), pt)
expect(ct.len()).to_equal(8u64)
```

</details>

#### encrypt then decrypt recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt: [u8] = [
    0x01u8, 0x23u8, 0x45u8, 0x67u8, 0x89u8, 0xabu8, 0xcdu8, 0xefu8,
    0xfeu8, 0xdcu8, 0xbau8, 0x98u8, 0x76u8, 0x54u8, 0x32u8, 0x10u8
]
val ct = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), pt)
val rt = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), ct)
expect(_bytes_hex(rt)).to_equal(_bytes_hex(pt))
```

</details>

### HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c)

#### output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hsalsa20(_hsalsa_key(), _hsalsa_input())
expect(out.len()).to_equal(32u64)
```

</details>

#### output matches NaCl reference vector byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = hsalsa20(_hsalsa_key(), _hsalsa_input())
expect(_bytes_hex(out)).to_equal(_bytes_hex(_hsalsa_expected()))
```

</details>

### XSalsa20 — computed byte-exact vector (Python-verified)

#### output length equals plaintext length (35 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), _xsalsa_plaintext())
expect(ct.len()).to_equal(35u64)
```

</details>

#### encryption matches computed ciphertext byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), _xsalsa_plaintext())
expect(_bytes_hex(ct)).to_equal(_bytes_hex(_xsalsa_expected_ct()))
```

</details>

### XSalsa20 — round-trip

#### encrypt then decrypt recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _xsalsa_plaintext()
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val rt = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), ct)
expect(_bytes_hex(rt)).to_equal(_bytes_hex(pt))
```

</details>

#### different keys produce different ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _xsalsa_plaintext()
val ct1 = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val ct2 = xsalsa20_xor(_make_key_zeros(), _xsalsa_nonce24(), pt)
expect(_bytes_hex(ct1) == _bytes_hex(ct2)).to_equal(false)
```

</details>

#### different nonces produce different ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _xsalsa_plaintext()
val ct1 = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val ct2 = xsalsa20_xor(_hsalsa_key(), _nonce24_alt(), pt)
expect(_bytes_hex(ct1) == _bytes_hex(ct2)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/salsa20_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0)
- Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0)
- Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce)
- Salsa20/20 XOR — round-trip and length
- HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c)
- XSalsa20 — computed byte-exact vector (Python-verified)
- XSalsa20 — round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
