# Hkdf Sha3 Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha3_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha3 Specification

## Scenarios

### HKDF-SHA3-256 — RFC 5869 §A.1-style

#### Extract is HMAC: hkdf_extract == hmac_sha3_256

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RFC 5869 §2.2: PRK = HMAC-Hash(salt, IKM)
val expected = hmac_sha3_256_bytes(_a1_salt(), _a1_ikm())
val actual = hkdf_extract_sha3_256(_a1_salt(), _a1_ikm())
expect(bytes_to_hex(actual)).to_equal(bytes_to_hex(expected))
```

</details>

#### Extract→Expand round-trip is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hkdf_sha3_256(_a1_salt(), _a1_ikm(), _a1_info(), 42)
val b = hkdf_sha3_256(_a1_salt(), _a1_ikm(), _a1_info(), 42)
expect(bytes_to_hex(a)).to_equal(bytes_to_hex(b))
```

</details>

#### Expand L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_256(_a1_salt(), _a1_ikm())
val okm = hkdf_expand_sha3_256(prk, _a1_info(), 0)
expect(okm.len()).to_equal(0)
```

</details>

#### Expand L>max(255*32) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_256(_a1_salt(), _a1_ikm())
val okm = hkdf_expand_sha3_256(prk, _a1_info(), 8161)
expect(okm.len()).to_equal(0)
```

</details>

#### OKM has exact requested length L=42

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val okm = hkdf_sha3_256(_a1_salt(), _a1_ikm(), _a1_info(), 42)
expect(okm.len()).to_equal(42)
```

</details>

### HKDF-SHA3-384 — RFC 5869 §A.1-style

#### Extract is HMAC: hkdf_extract == hmac_sha3_384

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = hmac_sha3_384_bytes(_a1_salt(), _a1_ikm())
val actual = hkdf_extract_sha3_384(_a1_salt(), _a1_ikm())
expect(bytes_to_hex(actual)).to_equal(bytes_to_hex(expected))
```

</details>

#### Extract→Expand round-trip is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hkdf_sha3_384(_a1_salt(), _a1_ikm(), _a1_info(), 42)
val b = hkdf_sha3_384(_a1_salt(), _a1_ikm(), _a1_info(), 42)
expect(bytes_to_hex(a)).to_equal(bytes_to_hex(b))
```

</details>

#### Expand L>max(255*48) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_384(_a1_salt(), _a1_ikm())
val okm = hkdf_expand_sha3_384(prk, _a1_info(), 12241)
expect(okm.len()).to_equal(0)
```

</details>

#### PRK length is 48 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_384(_a1_salt(), _a1_ikm())
expect(prk.len()).to_equal(48)
```

</details>

### HKDF-SHA3-512 — RFC 5869 §A.1-style

#### Extract is HMAC: hkdf_extract == hmac_sha3_512

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = hmac_sha3_512_bytes(_a1_salt(), _a1_ikm())
val actual = hkdf_extract_sha3_512(_a1_salt(), _a1_ikm())
expect(bytes_to_hex(actual)).to_equal(bytes_to_hex(expected))
```

</details>

#### Extract→Expand round-trip is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hkdf_sha3_512(_a1_salt(), _a1_ikm(), _a1_info(), 64)
val b = hkdf_sha3_512(_a1_salt(), _a1_ikm(), _a1_info(), 64)
expect(bytes_to_hex(a)).to_equal(bytes_to_hex(b))
```

</details>

#### Expand L>max(255*64) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_512(_a1_salt(), _a1_ikm())
val okm = hkdf_expand_sha3_512(prk, _a1_info(), 16321)
expect(okm.len()).to_equal(0)
```

</details>

#### PRK length is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk = hkdf_extract_sha3_512(_a1_salt(), _a1_ikm())
expect(prk.len()).to_equal(64)
```

</details>

#### Empty salt uses HashLen zero bytes per RFC 5869 §2.2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prk_empty_salt = hkdf_extract_sha3_512([], _a1_ikm())
val prk_zero_salt = hkdf_extract_sha3_512(_bytes_repeat(0, 64), _a1_ikm())
expect(bytes_to_hex(prk_empty_salt)).to_equal(bytes_to_hex(prk_zero_salt))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA3-256 — RFC 5869 §A.1-style
- HKDF-SHA3-384 — RFC 5869 §A.1-style
- HKDF-SHA3-512 — RFC 5869 §A.1-style

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
