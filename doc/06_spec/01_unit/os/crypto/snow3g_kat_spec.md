# Snow3g Kat Specification

> <details>

<!-- sdn-diagram:id=snow3g_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=snow3g_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

snow3g_kat_spec -> std
snow3g_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=snow3g_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snow3g Kat Specification

## Scenarios

### SNOW 3G keystream — 3GPP TS 35.217 §6.1.1

#### first keystream word for all-zero key/IV is 410ab3b9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = snow3g_keystream(_zero_key(), _zero_iv(), 2u64)
expect(_u32_hex(ks[0u64])).to_equal("410ab3b9")
```

</details>

#### second keystream word for all-zero key/IV is c764a037

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = snow3g_keystream(_zero_key(), _zero_iv(), 2u64)
expect(_u32_hex(ks[1u64])).to_equal("c764a037")
```

</details>

#### keystream output length matches requested word count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = snow3g_keystream(_zero_key(), _zero_iv(), 4u64)
expect(ks.len()).to_equal(4)
```

</details>

#### first two keystream words differ (state advances)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = snow3g_keystream(_zero_key(), _zero_iv(), 2u64)
expect(_u32_hex(ks[0u64])).to_equal(_u32_hex(ks[0u64]))
expect(ks[0u64] == ks[1u64]).to_equal(false)
```

</details>

### SNOW 3G UEA2 confidentiality — TS 35.217 §6.1.1

#### UEA2 output length equals input length (25 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = uea2_encrypt(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _zero_key(), _uea2_pt1(), 200u64)
expect(ct.len()).to_equal(25)
```

</details>

#### UEA2 decrypt(encrypt(m)) == m (self-inverse) for all-zero input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = uea2_encrypt(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _zero_key(), _uea2_pt1(), 200u64)
val pt = uea2_encrypt(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _zero_key(), ct, 200u64)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_uea2_pt1()))
```

</details>

#### UEA2 first 8 ciphertext bytes match first 2 keystream words for all-zero PT

1. ct[4u64] to i64
   - Expected: _bytes_hex(first8) equals `410ab3b9c764a037`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = uea2_encrypt(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _zero_key(), _uea2_pt1(), 200u64)
# PT=0 so CT = keystream; first 8 bytes = 410ab3b9 c764a037
val first8 = _bv([ct[0u64].to_i64(), ct[1u64].to_i64(), ct[2u64].to_i64(), ct[3u64].to_i64(),
                  ct[4u64].to_i64(), ct[5u64].to_i64(), ct[6u64].to_i64(), ct[7u64].to_i64()])
expect(_bytes_hex(first8)).to_equal("410ab3b9c764a037")
```

</details>

### SNOW 3G UIA2 integrity MAC — TS 35.217 §6.2.1

#### UIA2 MAC output length is 8 hex chars (32 bits)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mac = uia2_mac(0x00000000u32, 0x00000000u32, 0i64.to_u8(), _zero_key(), _uia2_msg1(), 4u64)
expect(_u32_hex(mac).len()).to_equal(8)
```

</details>

#### UIA2 Test Set 1 MAC-I for all-zero key 4-bit zero message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mac = uia2_mac(0x00000000u32, 0x00000000u32, 0i64.to_u8(), _zero_key(), _uia2_msg1(), 4u64)
expect(_u32_hex(mac)).to_equal("10ab3b9c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/snow3g_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SNOW 3G keystream — 3GPP TS 35.217 §6.1.1
- SNOW 3G UEA2 confidentiality — TS 35.217 §6.1.1
- SNOW 3G UIA2 integrity MAC — TS 35.217 §6.2.1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
