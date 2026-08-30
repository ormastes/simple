# Tea Specification

> <details>

<!-- sdn-diagram:id=tea_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tea_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tea_spec -> std
tea_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tea_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tea Specification

## Scenarios

### TEA — known-answer vectors

#### TEA: encrypt zero key + zero block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = tea_encrypt(_zero_key(), _zero_block())
expect(_bytes_to_hex(ct)).to_equal("41ea3a0a94baa940")
```

</details>

#### TEA: ciphertext is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = tea_encrypt(_zero_key(), _zero_block())
expect(ct.len()).to_equal(8)
```

</details>

#### TEA: decrypt zero key + known CT recovers zero block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = tea_decrypt(_zero_key(), _tea_zero_ct())
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### TEA: encrypt/decrypt round-trip (zero key)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = tea_encrypt(_zero_key(), _zero_block())
val pt = tea_decrypt(_zero_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### TEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = tea_encrypt(_seq_key(), _seq_block())
expect(_bytes_to_hex(ct)).to_equal("b1a1ab198c45fa5b")
```

</details>

#### TEA: encrypt/decrypt round-trip (seq key)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = tea_encrypt(_seq_key(), _seq_block())
val pt = tea_decrypt(_seq_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0102030405060708")
```

</details>

### XTEA — known-answer vectors

#### XTEA: encrypt zero key + zero block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xtea_encrypt(_zero_key(), _zero_block())
expect(_bytes_to_hex(ct)).to_equal("dee9d4d8f7131ed9")
```

</details>

#### XTEA: ciphertext is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xtea_encrypt(_zero_key(), _zero_block())
expect(ct.len()).to_equal(8)
```

</details>

#### XTEA: decrypt zero key + known CT recovers zero block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = xtea_decrypt(_zero_key(), _xtea_zero_ct())
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### XTEA: encrypt/decrypt round-trip (zero key)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xtea_encrypt(_zero_key(), _zero_block())
val pt = xtea_decrypt(_zero_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0000000000000000")
```

</details>

#### XTEA: encrypt seq key=0x000102..0F, plain=0x0102030405060708

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xtea_encrypt(_seq_key(), _seq_block())
expect(_bytes_to_hex(ct)).to_equal("88870e082874d853")
```

</details>

#### XTEA: encrypt/decrypt round-trip (seq key)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = xtea_encrypt(_seq_key(), _seq_block())
val pt = xtea_decrypt(_seq_key(), ct)
expect(_bytes_to_hex(pt)).to_equal("0102030405060708")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/tea_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TEA — known-answer vectors
- XTEA — known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
