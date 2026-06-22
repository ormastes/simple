# Seed Rfc4269 Kat Specification

> <details>

<!-- sdn-diagram:id=seed_rfc4269_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=seed_rfc4269_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

seed_rfc4269_kat_spec -> std
seed_rfc4269_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=seed_rfc4269_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Seed Rfc4269 Kat Specification

## Scenarios

### SEED RFC 4269 §B.1 (key=zeros, pt=0..F)

#### encrypt → 5ebac6e0054e166819aff1cc6d346cdb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b1_key(), _b1_pt())
expect(_bytes_hex(ct)).to_equal("5ebac6e0054e166819aff1cc6d346cdb")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b1_key(), _b1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b1_key(), _b1_pt())
val pt2 = seed_decrypt_block(_b1_key(), ct)
expect(_bytes_hex(pt2)).to_equal(_bytes_hex(_b1_pt()))
```

</details>

### SEED RFC 4269 §B.2 (key=0..F, pt=zeros)

#### encrypt → c11f22f20140505084483597e4370f43

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b2_key(), _b2_pt())
expect(_bytes_hex(ct)).to_equal("c11f22f20140505084483597e4370f43")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b2_key(), _b2_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b2_key(), _b2_pt())
val pt2 = seed_decrypt_block(_b2_key(), ct)
expect(_bytes_hex(pt2)).to_equal(_bytes_hex(_b2_pt()))
```

</details>

### SEED RFC 4269 §B.3 (key=4706..85, pt=83A2..7D)

#### encrypt → ee54d13ebcae706d226bc3142cd40d4a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b3_key(), _b3_pt())
expect(_bytes_hex(ct)).to_equal("ee54d13ebcae706d226bc3142cd40d4a")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b3_key(), _b3_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b3_key(), _b3_pt())
val pt2 = seed_decrypt_block(_b3_key(), ct)
expect(_bytes_hex(pt2)).to_equal(_bytes_hex(_b3_pt()))
```

</details>

### SEED RFC 4269 §B.4 (key=28DB..E7, pt=B41E..C7)

#### encrypt → 9b9b7bfcd1813cb95d0b3618f40f5122

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b4_key(), _b4_pt())
expect(_bytes_hex(ct)).to_equal("9b9b7bfcd1813cb95d0b3618f40f5122")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b4_key(), _b4_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = seed_encrypt_block(_b4_key(), _b4_pt())
val pt2 = seed_decrypt_block(_b4_key(), ct)
expect(_bytes_hex(pt2)).to_equal(_bytes_hex(_b4_pt()))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/seed_rfc4269_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SEED RFC 4269 §B.1 (key=zeros, pt=0..F)
- SEED RFC 4269 §B.2 (key=0..F, pt=zeros)
- SEED RFC 4269 §B.3 (key=4706..85, pt=83A2..7D)
- SEED RFC 4269 §B.4 (key=28DB..E7, pt=B41E..C7)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
