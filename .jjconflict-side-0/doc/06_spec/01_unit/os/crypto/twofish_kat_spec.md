# Twofish Kat Specification

> <details>

<!-- sdn-diagram:id=twofish_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=twofish_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

twofish_kat_spec -> std
twofish_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=twofish_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Twofish Kat Specification

## Scenarios

### Twofish — known-answer vectors (Twofish paper Table 4)

#### Twofish-128: encrypt all-zero key + all-zero PT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero16(), _zero16())
expect(_bytes_to_hex(ct)).to_equal("9f589f5cf6122c32b6bfec2f2ae8c35a")
```

</details>

#### Twofish-128: ciphertext is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero16(), _zero16())
expect(ct.len()).to_equal(16)
```

</details>

#### Twofish-128: decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero16(), _zero16())
val pt = twofish_decrypt_block(_zero16(), ct)
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-128: decrypt known ciphertext recovers all-zero PT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = twofish_decrypt_block(_zero16(), _ct_128_expected())
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-256: encrypt all-zero key + all-zero PT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero32(), _zero16())
expect(_bytes_to_hex(ct)).to_equal("57ff739d4dc92c1bd7fc01700cc8216f")
```

</details>

#### Twofish-256: ciphertext is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero32(), _zero16())
expect(ct.len()).to_equal(16)
```

</details>

#### Twofish-256: decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = twofish_encrypt_block(_zero32(), _zero16())
val pt = twofish_decrypt_block(_zero32(), ct)
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### Twofish-256: decrypt known ciphertext recovers all-zero PT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = twofish_decrypt_block(_zero32(), _ct_256_expected())
expect(_bytes_to_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/twofish_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Twofish — known-answer vectors (Twofish paper Table 4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
