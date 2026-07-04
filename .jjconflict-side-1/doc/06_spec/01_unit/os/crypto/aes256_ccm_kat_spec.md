# Aes256 Ccm Kat Specification

> <details>

<!-- sdn-diagram:id=aes256_ccm_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes256_ccm_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes256_ccm_kat_spec -> std
aes256_ccm_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes256_ccm_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Ccm Kat Specification

## Scenarios

### aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt

#### V1 encrypt: ciphertext bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
val ct = _slice_n(out, 0, 23)
expect(_bytes_hex(ct)).to_equal(
    "59615510a7c43bfb123d636b4613c03c6ce26907102a3f"
)
```

</details>

#### V1 encrypt: tag bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
val tag = _slice_n(out, 23, 8)
expect(_bytes_hex(tag)).to_equal("a9340731cd6d4ded")
```

</details>

#### V1 encrypt: output length is PT_len + tag_len

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
expect(out.len()).to_equal(31)
```

</details>

### aes256-ccm V1 -- decrypt round-trip and tamper detection

#### V1 decrypt: recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _unwrap_ok(aes256_ccm_decrypt(_v1_key(), _v1_nonce(), _empty(), _v1_ct(), _v1_tag()))
expect(_bytes_hex(pt)).to_equal(
    "08090a0b0c0d0e0f101112131415161718191a1b1c1d1e"
)
```

</details>

#### V1 decrypt with bad tag: returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = aes256_ccm_decrypt(_v1_key(), _v1_nonce(), _empty(), _v1_ct(), _v1_tag_bad())
expect(_is_err(r)).to_equal(true)
```

</details>

### aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt

#### V2 encrypt: ciphertext bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_pt(), 8u32)
val ct = _slice_n(out, 0, 24)
expect(_bytes_hex(ct)).to_equal(
    "e2b4b743093bcc3a5e57d76a9a769efcae191b14773af31a"
)
```

</details>

#### V2 encrypt: tag bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_pt(), 8u32)
val tag = _slice_n(out, 24, 8)
expect(_bytes_hex(tag)).to_equal("2273e08e81c40c6c")
```

</details>

#### V2 decrypt: recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _unwrap_ok(aes256_ccm_decrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_ct(), _v2_tag()))
expect(_bytes_hex(pt)).to_equal(
    "08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
)
```

</details>

### aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt

#### V3 encrypt: ciphertext bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_pt(), 12u32)
val ct = _slice_n(out, 0, 24)
expect(_bytes_hex(ct)).to_equal(
    "fc3ca91594f5e6bed5f6d005a89167a1718db3134f62ecee"
)
```

</details>

#### V3 encrypt: tag bytes match expected

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_pt(), 12u32)
val tag = _slice_n(out, 24, 12)
expect(_bytes_hex(tag)).to_equal("d86e61a7a9103d31a2bf1e69")
```

</details>

#### V3 decrypt: recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = _unwrap_ok(aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_ct(), _v3_tag()))
expect(_bytes_hex(pt)).to_equal(
    "202122232425262728292a2b2c2d2e2f3031323334353637"
)
```

</details>

#### V3 decrypt with tampered ciphertext: returns Err

1. var bad ct: [u8] = rt array new with cap
2. bad ct push
3. bad ct push
   - Expected: _is_err(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad_ct: [u8] = rt_array_new_with_cap(24)
bad_ct.push(0xFD)
var i: u64 = 1
while i < 24:
    bad_ct.push(_v3_ct()[i])
    i = i + 1
val r = aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), bad_ct, _v3_tag())
expect(_is_err(r)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/aes256_ccm_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt
- aes256-ccm V1 -- decrypt round-trip and tamper detection
- aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt
- aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
