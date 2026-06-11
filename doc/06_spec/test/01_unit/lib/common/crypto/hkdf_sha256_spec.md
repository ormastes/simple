# Hkdf Sha256 Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha256_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha256_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha256_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha256_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha256 Specification

## Scenarios

### HKDF-SHA-256 — RFC 5869 §A.1 (basic)

#### Extract PRK matches RFC 5869 §A.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_extract_sha256(_a1_salt(), _a1_ikm()))).to_equal(
    "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5")
```

</details>

#### Expand OKM(L=42) matches RFC 5869 §A.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_expand_sha256(_a1_prk(), _a1_info(), 42))).to_equal(
    "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
```

</details>

#### One-shot hkdf_sha256 OKM(L=42) matches RFC 5869 §A.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 42))).to_equal(
    "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
```

</details>

### HKDF-SHA-256 — RFC 5869 §A.2 (longer inputs)

#### Extract PRK matches RFC 5869 §A.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_extract_sha256(_a2_salt(), _a2_ikm()))).to_equal(
    "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244")
```

</details>

#### One-shot OKM(L=82) matches RFC 5869 §A.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha256(_a2_salt(), _a2_ikm(), _a2_info(), 82))).to_equal(
    "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87")
```

</details>

### HKDF-SHA-256 — RFC 5869 §A.3 (empty salt and info)

#### Extract PRK with empty salt matches RFC 5869 §A.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_extract_sha256([], _a1_ikm()))).to_equal(
    "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04")
```

</details>

#### One-shot OKM(L=42) with empty salt+info matches RFC 5869 §A.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha256([], _a1_ikm(), [], 42))).to_equal(
    "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8")
```

</details>

### HKDF-SHA-256 round-trip and boundaries

#### PRK is exactly 32 bytes (SHA-256 HashLen)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_extract_sha256(_a1_salt(), _a1_ikm()).len()).to_equal(32)
```

</details>

#### Two-step (Extract then Expand) equals one-shot hkdf_sha256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk  = hkdf_extract_sha256(_a1_salt(), _a1_ikm())
val okm1 = hkdf_expand_sha256(prk, _a1_info(), 42)
val okm2 = hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 42)
expect(bytes_to_hex(okm1)).to_equal(bytes_to_hex(okm2))
```

</details>

#### L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_expand_sha256(_a1_prk(), _a1_info(), 0).len()).to_equal(0)
```

</details>

#### L=1 returns exactly 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_expand_sha256(_a1_prk(), _a1_info(), 1).len()).to_equal(1)
```

</details>

#### L exceeding 255*32 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_expand_sha256(_a1_prk(), [], 255 * 32 + 1).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha256_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-256 — RFC 5869 §A.1 (basic)
- HKDF-SHA-256 — RFC 5869 §A.2 (longer inputs)
- HKDF-SHA-256 — RFC 5869 §A.3 (empty salt and info)
- HKDF-SHA-256 round-trip and boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
