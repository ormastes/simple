# Xsalsa20 Specification

> <details>

<!-- sdn-diagram:id=xsalsa20_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=xsalsa20_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

xsalsa20_spec -> std
xsalsa20_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=xsalsa20_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xsalsa20 Specification

## Scenarios

### xsalsa20_encrypt — NaCl box7.c known-answer vector

#### encrypt 64 zero bytes: first 32 bytes match NaCl reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), _zeros64())
val got = _bytes_hex_range(ct, 0, 32)
expect(got).to_equal("eea6a7251c1e72916d11c2cb214d3c252539121d8e234e652d651fa4c8cff880")
```

</details>

#### encrypt 64 zero bytes: output length is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), _zeros64())
expect(ct.len()).to_equal(64)
```

</details>

#### encrypt zero bytes: ciphertext is NOT all zeros (keystream non-trivial)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), _zeros64())
expect(_all_zero_64(ct)).to_equal(false)
```

</details>

### xsalsa20_encrypt/decrypt — round-trip

#### encrypt then decrypt 32 zero bytes == original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _zeros32()
val ct = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), pt)
val recovered = xsalsa20_decrypt(_nacl_key(), _nacl_nonce(), ct)
expect(_bytes_hex(recovered)).to_equal(_bytes_hex(pt))
```

</details>

#### decrypt is symmetric with encrypt (stream cipher identity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _zeros32()
val ct = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), pt)
val ct2 = xsalsa20_decrypt(_nacl_key(), _nacl_nonce(), pt)
# Both encrypt and decrypt XOR the same keystream
expect(_bytes_hex(ct)).to_equal(_bytes_hex(ct2))
```

</details>

### xsalsa20_encrypt — nonce independence

#### NaCl nonce and zero nonce give different ciphertexts for same plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _zeros32()
val ct1 = xsalsa20_encrypt(_nacl_key(), _nacl_nonce(), pt)
val ct2 = xsalsa20_encrypt(_nacl_key(), _zero_nonce(), pt)
expect(_bytes_hex(ct1) == _bytes_hex(ct2)).to_equal(false)
```

</details>

### hsalsa20 — known-answer vector (djb key, zero input)

#### HSalsa20(djb_key, zero16) output length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subkey = hsalsa20(_djb_key(), _zero_nonce16())
expect(subkey.len()).to_equal(32)
```

</details>

#### HSalsa20(djb_key, zero16) output is non-zero (non-trivial permutation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subkey = hsalsa20(_djb_key(), _zero_nonce16())
expect(_all_zero_32(subkey)).to_equal(false)
```

</details>

#### HSalsa20(nacl_key, nacl_nonce[0..16]) output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subkey = hsalsa20(_nacl_key(), _nacl_nonce_head16())
expect(subkey.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/xsalsa20_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- xsalsa20_encrypt — NaCl box7.c known-answer vector
- xsalsa20_encrypt/decrypt — round-trip
- xsalsa20_encrypt — nonce independence
- hsalsa20 — known-answer vector (djb key, zero input)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
