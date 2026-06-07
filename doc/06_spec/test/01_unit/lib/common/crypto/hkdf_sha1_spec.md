# Hkdf Sha1 Specification

> <details>

<!-- sdn-diagram:id=hkdf_sha1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hkdf_sha1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hkdf_sha1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hkdf_sha1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hkdf Sha1 Specification

## Scenarios

### HKDF-SHA-1 — RFC 5869 §A.4 (basic)

#### Extract PRK = 9b6c18c432a7bf8f0e71c8eb88f4b30baa2ba243

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# salt = 0x000102030405060708090a0b0c (13 bytes)
# ikm  = 11 * 0x0b   (RFC 5869 §A.4 specifies 11 bytes, not 22)
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
expect(bytes_to_hex(hkdf_extract_sha1(salt, _ikm_11_0b()))).to_equal(
    "9b6c18c432a7bf8f0e71c8eb88f4b30baa2ba243"
)
```

</details>

#### Expand OKM(L=42) = 085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2c22e422478d305f3f896

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# info = 0xf0f1f2f3f4f5f6f7f8f9 (10 bytes), L = 42
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
expect(bytes_to_hex(hkdf_sha1(salt, _ikm_11_0b(), info, 42))).to_equal(
    "085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2c22e422478d305f3f896"
)
```

</details>

### HKDF-SHA-1 — RFC 5869 §A.5 (long inputs)

#### Extract PRK = 8adae09a2a307059478d309b26c4115a224cfaf6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_extract_sha1(_a5_salt(), _a5_ikm()))).to_equal(
    "8adae09a2a307059478d309b26c4115a224cfaf6"
)
```

</details>

#### Expand OKM(L=82) matches RFC 5869 §A.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha1(_a5_salt(), _a5_ikm(), _a5_info(), 82))).to_equal(
    "0bd770a74d1160f7c9f12cd5912a06ebff6adcae899d92191fe4305673ba2ffe8fa3f1a4e5ad79f3f334b3b202b2173c486ea37ce3d397ed034c7f9dfeb15c5e927336d0441f4c4300e2cff0d0900b52d3b4"
)
```

</details>

### HKDF-SHA-1 — RFC 5869 §A.6 (empty salt and info)

#### Extract PRK with empty salt = da8c8a73c7fa77288ec6f5e7c297786aa0d32d01

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty salt -> HashLen (20) zero bytes per RFC 5869 §2.2
expect(bytes_to_hex(hkdf_extract_sha1([], _ikm_22_0b()))).to_equal(
    "da8c8a73c7fa77288ec6f5e7c297786aa0d32d01"
)
```

</details>

#### Expand OKM(L=42) = 0ac1af7002b3d761d1e55298da9d0506b9ae52057220a306e07b6b87e8df21d0ea00033de03984d34918

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha1([], _ikm_22_0b(), [], 42))).to_equal(
    "0ac1af7002b3d761d1e55298da9d0506b9ae52057220a306e07b6b87e8df21d0ea00033de03984d34918"
)
```

</details>

### HKDF-SHA-1 — RFC 5869 §A.7 (explicit zero salt)

#### Extract PRK = 2adccada18779e7c2077ad2eb19d3f3e731385dd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_extract_sha1(_zeros_20(), _ikm_22_0c()))).to_equal(
    "2adccada18779e7c2077ad2eb19d3f3e731385dd"
)
```

</details>

#### Expand OKM(L=42) = 2c91117204d745f3500d636a62f64f0ab3bae548aa53d423b0d1f27ebba6f5e5673a081d70cce7acfc48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(hkdf_sha1(_zeros_20(), _ikm_22_0c(), [], 42))).to_equal(
    "2c91117204d745f3500d636a62f64f0ab3bae548aa53d423b0d1f27ebba6f5e5673a081d70cce7acfc48"
)
```

</details>

### HKDF-SHA-1 round-trip and boundaries

#### Two-step (Extract then Expand) equals combined hkdf_sha1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
val prk = hkdf_extract_sha1(salt, _ikm_22_0b())
val two_step = hkdf_expand_sha1(prk, info, 42)
val combined = hkdf_sha1(salt, _ikm_22_0b(), info, 42)
expect(bytes_to_hex(two_step)).to_equal(bytes_to_hex(combined))
```

</details>

#### Extract PRK is exactly 20 bytes (SHA-1 HashLen)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hkdf_extract_sha1([], _ikm_22_0b()).len()).to_equal(20)
```

</details>

#### L=0 returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
expect(hkdf_sha1(salt, _ikm_22_0b(), info, 0).len()).to_equal(0)
```

</details>

#### L=1 returns exactly 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
expect(hkdf_sha1(salt, _ikm_22_0b(), info, 1).len()).to_equal(1)
```

</details>

#### L exceeding 255*20 (5100) returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val salt = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c]
val info = [0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9]
expect(hkdf_sha1(salt, _ikm_22_0b(), info, 5101).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/hkdf_sha1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HKDF-SHA-1 — RFC 5869 §A.4 (basic)
- HKDF-SHA-1 — RFC 5869 §A.5 (long inputs)
- HKDF-SHA-1 — RFC 5869 §A.6 (empty salt and info)
- HKDF-SHA-1 — RFC 5869 §A.7 (explicit zero salt)
- HKDF-SHA-1 round-trip and boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
