# Aes256 Simd Round Specification

> 1. expect  at

<!-- sdn-diagram:id=aes256_simd_round_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes256_simd_round_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes256_simd_round_spec -> std
aes256_simd_round_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes256_simd_round_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Simd Round Specification

## Scenarios

### AES-256 SIMD round path (W6-A simd_aes_round + simd_aes_round_last × 14)

### FIPS 197 §C.3 single-block KAT

#### encrypts PT 00..ff with key 00..1f to CT 8ea2b7ca5167 45bfeafc49904b496089

1. expect  at
2. expect  at
3. expect  at
4. expect  at
5. expect  at
6. expect  at
7. expect  at
8. expect  at
9. expect  at
10. expect  at
11. expect  at
12. expect  at
13. expect  at
14. expect  at
15. expect  at
16. expect  at


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_encrypt_block(fips197_c3_pt(), fips197_c3_key())
expect _at(ct, 0)  == 0x8eu8
expect _at(ct, 1)  == 0xa2u8
expect _at(ct, 2)  == 0xb7u8
expect _at(ct, 3)  == 0xcau8
expect _at(ct, 4)  == 0x51u8
expect _at(ct, 5)  == 0x67u8
expect _at(ct, 6)  == 0x45u8
expect _at(ct, 7)  == 0xbfu8
expect _at(ct, 8)  == 0xeau8
expect _at(ct, 9)  == 0xfcu8
expect _at(ct, 10) == 0x49u8
expect _at(ct, 11) == 0x90u8
expect _at(ct, 12) == 0x4bu8
expect _at(ct, 13) == 0x49u8
expect _at(ct, 14) == 0x60u8
expect _at(ct, 15) == 0x89u8
```

</details>

### NIST SP 800-38A §F.1.5 ECB-AES256.Encrypt vectors

#### block 1: 6bc1bee2...172a -> f3eed1bd...81f8

1. expect  at
2. expect  at
3. expect  at
4. expect  at
5. expect  at
6. expect  at
7. expect  at
8. expect  at
9. expect  at
10. expect  at
11. expect  at
12. expect  at
13. expect  at
14. expect  at
15. expect  at
16. expect  at


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_encrypt_block(sp80038a_pt1(), sp80038a_key())
expect _at(ct, 0)  == 0xf3u8
expect _at(ct, 1)  == 0xeeu8
expect _at(ct, 2)  == 0xd1u8
expect _at(ct, 3)  == 0xbdu8
expect _at(ct, 4)  == 0xb5u8
expect _at(ct, 5)  == 0xd2u8
expect _at(ct, 6)  == 0xa0u8
expect _at(ct, 7)  == 0x3cu8
expect _at(ct, 8)  == 0x06u8
expect _at(ct, 9)  == 0x4bu8
expect _at(ct, 10) == 0x5au8
expect _at(ct, 11) == 0x7eu8
expect _at(ct, 12) == 0x3du8
expect _at(ct, 13) == 0xb1u8
expect _at(ct, 14) == 0x81u8
expect _at(ct, 15) == 0xf8u8
```

</details>

#### block 2: ae2d8a57...8e51 -> 591ccb10...2870

1. expect  at
2. expect  at
3. expect  at
4. expect  at
5. expect  at
6. expect  at
7. expect  at
8. expect  at
9. expect  at
10. expect  at
11. expect  at
12. expect  at
13. expect  at
14. expect  at
15. expect  at
16. expect  at


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_encrypt_block(sp80038a_pt2(), sp80038a_key())
expect _at(ct, 0)  == 0x59u8
expect _at(ct, 1)  == 0x1cu8
expect _at(ct, 2)  == 0xcbu8
expect _at(ct, 3)  == 0x10u8
expect _at(ct, 4)  == 0xd4u8
expect _at(ct, 5)  == 0x10u8
expect _at(ct, 6)  == 0xedu8
expect _at(ct, 7)  == 0x26u8
expect _at(ct, 8)  == 0xdcu8
expect _at(ct, 9)  == 0x5bu8
expect _at(ct, 10) == 0xa7u8
expect _at(ct, 11) == 0x4au8
expect _at(ct, 12) == 0x31u8
expect _at(ct, 13) == 0x36u8
expect _at(ct, 14) == 0x28u8
expect _at(ct, 15) == 0x70u8
```

</details>

#### block 3: 30c81c46...52ef -> b6ed21b9...ed1d

1. expect  at
2. expect  at
3. expect  at
4. expect  at
5. expect  at
6. expect  at
7. expect  at
8. expect  at
9. expect  at
10. expect  at
11. expect  at
12. expect  at
13. expect  at
14. expect  at
15. expect  at
16. expect  at


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_encrypt_block(sp80038a_pt3(), sp80038a_key())
expect _at(ct, 0)  == 0xb6u8
expect _at(ct, 1)  == 0xedu8
expect _at(ct, 2)  == 0x21u8
expect _at(ct, 3)  == 0xb9u8
expect _at(ct, 4)  == 0x9cu8
expect _at(ct, 5)  == 0xa6u8
expect _at(ct, 6)  == 0xf4u8
expect _at(ct, 7)  == 0xf9u8
expect _at(ct, 8)  == 0xf1u8
expect _at(ct, 9)  == 0x53u8
expect _at(ct, 10) == 0xe7u8
expect _at(ct, 11) == 0xb1u8
expect _at(ct, 12) == 0xbeu8
expect _at(ct, 13) == 0xafu8
expect _at(ct, 14) == 0xedu8
expect _at(ct, 15) == 0x1du8
```

</details>

#### block 4: f69f2445...3710 -> 23304b7a...ecc7

1. expect  at
2. expect  at
3. expect  at
4. expect  at
5. expect  at
6. expect  at
7. expect  at
8. expect  at
9. expect  at
10. expect  at
11. expect  at
12. expect  at
13. expect  at
14. expect  at
15. expect  at
16. expect  at


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_encrypt_block(sp80038a_pt4(), sp80038a_key())
expect _at(ct, 0)  == 0x23u8
expect _at(ct, 1)  == 0x30u8
expect _at(ct, 2)  == 0x4bu8
expect _at(ct, 3)  == 0x7au8
expect _at(ct, 4)  == 0x39u8
expect _at(ct, 5)  == 0xf9u8
expect _at(ct, 6)  == 0xf3u8
expect _at(ct, 7)  == 0xffu8
expect _at(ct, 8)  == 0x06u8
expect _at(ct, 9)  == 0x7du8
expect _at(ct, 10) == 0x8du8
expect _at(ct, 11) == 0x8fu8
expect _at(ct, 12) == 0x9eu8
expect _at(ct, 13) == 0x24u8
expect _at(ct, 14) == 0xecu8
expect _at(ct, 15) == 0xc7u8
```

</details>

### round-step sanity (W6-A primitive reused for AES-256)

#### simd_aes_round_last(zero, zero) returns S-box(0)=0x63 in every lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SubBytes(ShiftRows(0)) XOR 0 = SBOX[0] = 0x63 — same kernel as
# AES-128 since round count and key schedule are the only diff.
val z = Vec16u8.zero()
val r = simd_aes_round_last(z, z)
expect r.u0  == 0x63u8
expect r.u1  == 0x63u8
expect r.u7  == 0x63u8
expect r.u8_ == 0x63u8
expect r.u15 == 0x63u8
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes256_simd_round_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-256 SIMD round path (W6-A simd_aes_round + simd_aes_round_last × 14)
- FIPS 197 §C.3 single-block KAT
- NIST SP 800-38A §F.1.5 ECB-AES256.Encrypt vectors
- round-step sanity (W6-A primitive reused for AES-256)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
