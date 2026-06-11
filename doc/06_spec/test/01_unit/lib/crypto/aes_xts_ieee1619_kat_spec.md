# Aes Xts Ieee1619 Kat Specification

> <details>

<!-- sdn-diagram:id=aes_xts_ieee1619_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_xts_ieee1619_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_xts_ieee1619_kat_spec -> std
aes_xts_ieee1619_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_xts_ieee1619_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Xts Ieee1619 Kat Specification

## Scenarios

### AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0)

#### encrypts plaintext to TV1 ciphertext (917cf69e…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_pt())).to_equal(_tv1_ct())
```

</details>

#### decrypts TV1 ciphertext back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_decrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_ct())).to_equal(_tv1_pt())
```

</details>

#### round-trips encrypt(decrypt(C)) == C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes128_xts_decrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_ct())
expect(aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, pt)).to_equal(_tv1_ct())
```

</details>

### AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333)

#### encrypts plaintext to TV2 ciphertext (c454185e…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_encrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_pt())).to_equal(_tv2_ct())
```

</details>

#### decrypts TV2 ciphertext back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_decrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_ct())).to_equal(_tv2_pt())
```

</details>

### AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333)

#### encrypts plaintext to TV3 ciphertext (af85336b…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_encrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_pt())).to_equal(_tv3_ct())
```

</details>

#### decrypts TV3 ciphertext back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_decrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_ct())).to_equal(_tv3_pt())
```

</details>

### AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling

#### encrypts 512-byte sector to TV4 ciphertext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_encrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_pt())).to_equal(_tv4_ct())
```

</details>

#### decrypts TV4 ciphertext back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_decrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_ct())).to_equal(_tv4_pt())
```

</details>

### AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff)

#### encrypts 512-byte sector to TV10 ciphertext (1c3b3a10…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_pt())).to_equal(_tv5_ct())
```

</details>

#### decrypts TV10 ciphertext back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes256_xts_decrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_ct())).to_equal(_tv5_pt())
```

</details>

#### round-trips encrypt(decrypt(C)) == C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes256_xts_decrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_ct())
expect(aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, pt)).to_equal(_tv5_ct())
```

</details>

### AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a)

#### encrypts 17-byte plaintext via CTS to ciphertext (6c1625db…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# IEEE 1619 §5.4: one full block + 1-byte partial; CTS swaps last two
# output groups in computation but emits them in plaintext order.
expect(aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_pt())).to_equal(_cts17_ct())
```

</details>

#### decrypts 17-byte ciphertext via CTS back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_xts_decrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_ct())).to_equal(_cts17_pt())
```

</details>

#### round-trips CTS encrypt(decrypt(C)) == C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes128_xts_decrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_ct())
expect(aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, pt)).to_equal(_cts17_ct())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0)
- AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333)
- AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333)
- AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling
- AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff)
- AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
