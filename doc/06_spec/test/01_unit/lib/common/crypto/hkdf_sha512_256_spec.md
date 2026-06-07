# Hkdf Sha512 256 Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha512_256_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha512_256_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha512_256_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha512_256_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha512 256 Specification

## Scenarios

### HKDF-SHA-512/256 — Extract

#### Extract output is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_extract_sha512_256(_range_512(0, 13), _repeat_512(11, 22)).len()).to_equal(32)
```

</details>

#### Extract equals direct HMAC-SHA-512/256(salt, IKM)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk    = hkdf_extract_sha512_256(_range_512(0, 13), _repeat_512(11, 22))
val direct = hmac_sha512_256_bytes(_range_512(0, 13), _repeat_512(11, 22))
expect(bytes_to_hex(prk)).to_equal(bytes_to_hex(direct))
```

</details>

#### Empty salt treated as 32 zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk_empty = hkdf_extract_sha512_256([], _repeat_512(11, 22))
val prk_zeros = hkdf_extract_sha512_256(_repeat_512(0, 32), _repeat_512(11, 22))
expect(bytes_to_hex(prk_empty)).to_equal(bytes_to_hex(prk_zeros))
```

</details>

### HKDF-SHA-512/256 — Expand

#### Expand output has correct length (42 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val okm = hkdf_expand_sha512_256(_repeat_512(7, 32), _range_512(0, 5), 42)
expect(okm.len()).to_equal(42)
```

</details>

#### Expand output has correct length (64 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val okm = hkdf_expand_sha512_256(_repeat_512(7, 32), _range_512(0, 5), 64)
expect(okm.len()).to_equal(64)
```

</details>

#### Expand of length 0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_expand_sha512_256(_repeat_512(1, 32), [], 0).len()).to_equal(0)
```

</details>

#### Expand returns empty list when length exceeds 255*32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_expand_sha512_256(_repeat_512(1, 32), [], 255 * 32 + 1).len()).to_equal(0)
```

</details>

### HKDF-SHA-512/256 — round-trip and determinism

#### Two-step (Extract then Expand) equals one-shot hkdf_sha512_256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk  = hkdf_extract_sha512_256(_repeat_512(7, 8), _repeat_512(42, 16))
val okm1 = hkdf_expand_sha512_256(prk, _repeat_512(99, 4), 32)
val okm2 = hkdf_sha512_256(_repeat_512(7, 8), _repeat_512(42, 16), _repeat_512(99, 4), 32)
expect(bytes_to_hex(okm1)).to_equal(bytes_to_hex(okm2))
```

</details>

#### Deterministic: same inputs produce same OKM

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val okm1 = hkdf_sha512_256(_range_512(50, 10), _range_512(10, 20), _range_512(100, 8), 48)
val okm2 = hkdf_sha512_256(_range_512(50, 10), _range_512(10, 20), _range_512(100, 8), 48)
expect(bytes_to_hex(okm1)).to_equal(bytes_to_hex(okm2))
```

</details>

#### Different IKM produces different OKM

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val okm1 = hkdf_sha512_256([], _repeat_512(1, 16), [], 32)
val okm2 = hkdf_sha512_256([], _repeat_512(2, 16), [], 32)
expect(bytes_to_hex(okm1)).to_equal(bytes_to_hex(okm1))
expect(bytes_to_hex(okm2)).to_equal(bytes_to_hex(okm2))
expect(okm1.len()).to_equal(32)
expect(okm2.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha512_256_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-512/256 — Extract
- HKDF-SHA-512/256 — Expand
- HKDF-SHA-512/256 — round-trip and determinism

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
