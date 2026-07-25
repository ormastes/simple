# Hkdf Rfc5869 Specification

> <details>

<!-- sdn-diagram:id=hkdf_rfc5869_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_rfc5869_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_rfc5869_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_rfc5869_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Rfc5869 Specification

## Scenarios

### HKDF-SHA-256 RFC 5869 Appendix A vectors

#### A.1 PRK — explicit salt → 077709362c...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.1 PRK = 077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5
expect(bytes_to_hex(hkdf_extract_sha256(_a1_salt(), _a1_ikm()))).to_equal(
    "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
)
```

</details>

#### A.1 OKM — L=42 → 3cb25f25...

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.1 OKM (42 bytes)
# 3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865
expect(bytes_to_hex(hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 42))).to_equal(
    "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
)
```

</details>

#### A.3 PRK — empty salt → 19ef24a3...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.3 PRK = 19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04
expect(bytes_to_hex(hkdf_extract_sha256([], _a3_ikm()))).to_equal(
    "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"
)
```

</details>

#### A.3 OKM — empty salt + empty info L=42 → 8da4e775...

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.3 OKM (42 bytes)
# 8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8
expect(bytes_to_hex(hkdf_sha256([], _a3_ikm(), [], 42))).to_equal(
    "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"
)
```

</details>

#### A.2 PRK — long inputs → 06a6b88c...

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.2 PRK = 06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244
expect(bytes_to_hex(hkdf_extract_sha256(_a2_salt(), _a2_ikm()))).to_equal(
    "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244"
)
```

</details>

#### A.2 OKM — long inputs L=82 → b11e398d...

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §A.2 OKM (82 bytes)
# b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c
# 59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71
# cc30c58179ec3e87c14c01d5c1f3434f1d87
expect(bytes_to_hex(hkdf_sha256(_a2_salt(), _a2_ikm(), _a2_info(), 82))).to_equal(
    "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87"
)
```

</details>

### HKDF-SHA-256 boundary cases

#### L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 0).len()).to_equal(0)
```

</details>

#### L=1 returns exactly 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 1).len()).to_equal(1)
```

</details>

#### L exceeding 255*32 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_sha256(_a1_salt(), _a1_ikm(), _a1_info(), 8161).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/hkdf_rfc5869_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-256 RFC 5869 Appendix A vectors
- HKDF-SHA-256 boundary cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
