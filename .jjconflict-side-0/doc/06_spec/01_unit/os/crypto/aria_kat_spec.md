# Aria Kat Specification

> <details>

<!-- sdn-diagram:id=aria_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aria_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aria_kat_spec -> std
aria_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aria_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aria Kat Specification

## Scenarios

### ARIA RFC 5794 §B.1 — ARIA-128

#### encrypt → c6ecd08e22c30abdb215cf74e2075e6e

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
expect(_bytes_hex(ct)).to_equal("c6ecd08e22c30abdb215cf74e2075e6e")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trips to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b1_key(), _b1_pt())
val pt = aria_decrypt_block(_b1_key(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_b1_pt()))
```

</details>

#### decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aria_decrypt_block(_b1_key(), _b1_ct())
expect(_bytes_hex(pt)).to_equal("11111111aaaaaaaa11111111bbbbbbbb")
```

</details>

### ARIA RFC 5794 §B.3 — ARIA-256

#### encrypt → 58a875e6044ad7fffa4f58420f7f442d

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
expect(_bytes_hex(ct)).to_equal("58a875e6044ad7fffa4f58420f7f442d")
```

</details>

#### output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### decrypt round-trips to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aria_encrypt_block(_b3_key(), _b1_pt())
val pt = aria_decrypt_block(_b3_key(), ct)
expect(_bytes_hex(pt)).to_equal(_bytes_hex(_b1_pt()))
```

</details>

#### decrypt known ciphertext → 11111111aaaaaaaa11111111bbbbbbbb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aria_decrypt_block(_b3_key(), _b3_ct())
expect(_bytes_hex(pt)).to_equal("11111111aaaaaaaa11111111bbbbbbbb")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/aria_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARIA RFC 5794 §B.1 — ARIA-128
- ARIA RFC 5794 §B.3 — ARIA-256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
