# Salsa20 Kat Specification

> <details>

<!-- sdn-diagram:id=salsa20_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=salsa20_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

salsa20_kat_spec -> std
salsa20_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=salsa20_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Salsa20 Kat Specification

## Scenarios

### Salsa20/20 ECRYPT Set 1 Vector 0 — key=0x80..., nonce=0

#### block 0 keystream matches ECRYPT test vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(salsa20_20_block(_key_s1v0(), _nonce_zero8(), 0u32, 0u32)).to_equal(_expected_s1v0_block0())
```

</details>

### Salsa20/20 ECRYPT Set 2 Vector 0 — all-zero key and nonce

#### block 0 keystream matches ECRYPT test vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(salsa20_20_block(_key_zero32(), _nonce_zero8(), 0u32, 0u32)).to_equal(_expected_s2v0_block0())
```

</details>

### Salsa20/20 block output length

#### salsa20_20_block always returns exactly 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(salsa20_20_block(_key_zero32(), _nonce_zero8(), 0u32, 0u32).len()).to_equal(64)
```

</details>

### Salsa20/20 XOR round-trip

#### encrypt then decrypt with same key/nonce returns original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _key_s1v0()
val nonce = _nonce_zero8()
val msg = _repeat_byte(0x42u8, 64)
val ct = salsa20_20_xor(key, nonce, msg)
val pt = salsa20_20_xor(key, nonce, ct)
expect(pt).to_equal(msg)
```

</details>

### salsa20_xor alias

#### salsa20_xor equals salsa20_20_xor for same inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _key_s1v0()
val nonce = _nonce_zero8()
val msg = _repeat_byte(0x00u8, 32)
expect(salsa20_xor(key, nonce, msg)).to_equal(salsa20_20_xor(key, nonce, msg))
```

</details>

### HSalsa20 all-zero input

#### HSalsa20(0^32, 0^16) matches NaCl reference output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input_zero = _repeat_byte(0x00u8, 16)
expect(hsalsa20(_key_zero32(), input_zero)).to_equal(_hsalsa20_expected_zero())
```

</details>

### HSalsa20 output length

#### hsalsa20 always returns exactly 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input_zero = _repeat_byte(0x00u8, 16)
expect(hsalsa20(_key_zero32(), input_zero).len()).to_equal(32)
```

</details>

### XSalsa20 libsodium stream vector

#### XSalsa20 keystream first 32 bytes match libsodium test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = xsalsa20_xor(_xsalsa20_key(), _xsalsa20_nonce(), _repeat_byte(0x00u8, 32))
expect(ks).to_equal(_xsalsa20_expected_first32())
```

</details>

### XSalsa20 XOR round-trip

#### encrypt then decrypt with same key/nonce returns original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _xsalsa20_key()
val nonce = _xsalsa20_nonce()
val msg = _repeat_byte(0x61u8, 64)
val ct = xsalsa20_xor(key, nonce, msg)
val pt = xsalsa20_xor(key, nonce, ct)
expect(pt).to_equal(msg)
```

</details>

### XSalsa20 output length

#### xsalsa20_xor output same length as input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _repeat_byte(0x00u8, 77)
val ct = xsalsa20_xor(_xsalsa20_key(), _xsalsa20_nonce(), msg)
expect(ct.len()).to_equal(77)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/salsa20_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Salsa20/20 ECRYPT Set 1 Vector 0 — key=0x80..., nonce=0
- Salsa20/20 ECRYPT Set 2 Vector 0 — all-zero key and nonce
- Salsa20/20 block output length
- Salsa20/20 XOR round-trip
- salsa20_xor alias
- HSalsa20 all-zero input
- HSalsa20 output length
- XSalsa20 libsodium stream vector
- XSalsa20 XOR round-trip
- XSalsa20 output length

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
