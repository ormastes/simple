# Aes Modes Nist Specification

> <details>

<!-- sdn-diagram:id=aes_modes_nist_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_modes_nist_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_modes_nist_spec -> std
aes_modes_nist_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_modes_nist_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Modes Nist Specification

## Scenarios

### AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors

#### F.4.1 block 1 OFB-AES-128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_ofb128_ct(), 0))
```

</details>

#### F.4.1 block 2 OFB-AES-128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_ofb128_ct(), 1))
```

</details>

#### F.4.1 block 3 OFB-AES-128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_ofb128_ct(), 2))
```

</details>

#### F.4.1 block 4 OFB-AES-128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_ofb128_ct(), 3))
```

</details>

#### F.4.2 OFB-AES-128 decrypt round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes128_ofb_decrypt(_key128(), _iv(), _ofb128_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors

#### F.4.5 block 1 OFB-AES-256 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_ofb256_ct(), 0))
```

</details>

#### F.4.5 block 2 OFB-AES-256 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_ofb256_ct(), 1))
```

</details>

#### F.4.5 block 3 OFB-AES-256 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_ofb256_ct(), 2))
```

</details>

#### F.4.5 block 4 OFB-AES-256 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_ofb256_ct(), 3))
```

</details>

#### F.4.6 OFB-AES-256 decrypt round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes256_ofb_decrypt(_key256(), _iv(), _ofb256_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors

#### F.3.13 block 1 AES-128-CFB128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_cfb128_128_ct(), 0))
```

</details>

#### F.3.13 block 2 AES-128-CFB128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_cfb128_128_ct(), 1))
```

</details>

#### F.3.13 block 3 AES-128-CFB128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_cfb128_128_ct(), 2))
```

</details>

#### F.3.13 block 4 AES-128-CFB128 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_cfb128_128_ct(), 3))
```

</details>

#### F.3.14 AES-128-CFB128 decrypt round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes128_cfb128_decrypt(_key128(), _iv(), _cfb128_128_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB128-256 vectors (verified)

#### AES-256-CFB128 block 1 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_cfb128_256_ct(), 0))
```

</details>

#### AES-256-CFB128 block 2 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_cfb128_256_ct(), 1))
```

</details>

#### AES-256-CFB128 block 3 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_cfb128_256_ct(), 2))
```

</details>

#### AES-256-CFB128 block 4 encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_cfb128_256_ct(), 3))
```

</details>

#### AES-256-CFB128 decrypt round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes256_cfb128_decrypt(_key256(), _iv(), _cfb128_256_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors

#### F.3.7 AES-128-CFB8 encrypts 18-byte plaintext correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes128_cfb8_encrypt(_key128(), _iv(), _cfb8_pt())
expect(ct).to_equal(_cfb8_ct())
```

</details>

#### F.3.8 AES-128-CFB8 decrypts back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes128_cfb8_decrypt(_key128(), _iv(), _cfb8_ct())
expect(pt).to_equal(_cfb8_pt())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/aes_modes_nist_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors
- AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors
- AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors
- AES-CFB128-256 vectors (verified)
- AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
