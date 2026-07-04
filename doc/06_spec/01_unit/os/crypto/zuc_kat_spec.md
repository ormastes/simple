# Zuc Kat Specification

> <details>

<!-- sdn-diagram:id=zuc_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zuc_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zuc_kat_spec -> std
zuc_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zuc_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zuc Kat Specification

## Scenarios

### ZUC-128 keystream — 3GPP TS 35.223 Annex A

#### first keystream word for all-zero key/IV is 27bede74

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = zuc_keystream(_zuc_zero_key(), _zuc_zero_iv(), 2u64)
expect(_u32_hex(ks[0u64])).to_equal("27bede74")
```

</details>

#### second keystream word for all-zero key/IV is 018082da

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = zuc_keystream(_zuc_zero_key(), _zuc_zero_iv(), 2u64)
expect(_u32_hex(ks[1u64])).to_equal("018082da")
```

</details>

#### keystream output length matches requested word count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ks = zuc_keystream(_zuc_zero_key(), _zuc_zero_iv(), 4u64)
expect(ks.len()).to_equal(4)
```

</details>

### ZUC EEA3 confidentiality — TS 35.223 §6.1.1

#### EEA3 Test Set 1 ciphertext matches TS 35.223 §6.1.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = eea3_encrypt(0x66035492u32, 0x0Fi64.to_u8(), 0i64.to_u8(), _eea3_ck1(), _eea3_pt1(), 193u64)
expect(_bytes_hex(ct)).to_equal(_eea3_ct1_expected())
```

</details>

#### EEA3 output length equals input length (25 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = eea3_encrypt(0x66035492u32, 0x0Fi64.to_u8(), 0i64.to_u8(), _eea3_ck1(), _eea3_pt1(), 193u64)
expect(ct.len()).to_equal(25)
```

</details>

#### EEA3 decrypt(encrypt(m)) == m (self-inverse)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = eea3_encrypt(0x66035492u32, 0x0Fi64.to_u8(), 0i64.to_u8(), _eea3_ck1(), _eea3_pt1(), 193u64)
val pt = eea3_encrypt(0x66035492u32, 0x0Fi64.to_u8(), 0i64.to_u8(), _eea3_ck1(), ct, 193u64)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_eea3_pt1_masked()))
```

</details>

### ZUC EIA3 integrity MAC — TS 35.223 §6.2.1

#### EIA3 MAC output length is 8 hex chars (32 bits)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mac = eia3_mac(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _eia3_ik1(), _eia3_msg1(), 1u64)
expect(_u32_hex(mac).len()).to_equal(8)
```

</details>

#### EIA3 Test Set 1 MAC-I for all-zero key 1-bit zero message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mac = eia3_mac(0x00000000u32, 0x00i64.to_u8(), 0i64.to_u8(), _eia3_ik1(), _eia3_msg1(), 1u64)
expect(_u32_hex(mac)).to_equal("c8a9595e")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/zuc_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ZUC-128 keystream — 3GPP TS 35.223 Annex A
- ZUC EEA3 confidentiality — TS 35.223 §6.1.1
- ZUC EIA3 integrity MAC — TS 35.223 §6.2.1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
