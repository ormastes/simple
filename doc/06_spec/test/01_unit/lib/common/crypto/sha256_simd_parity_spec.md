# Sha256 Simd Parity Specification

> <details>

<!-- sdn-diagram:id=sha256_simd_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha256_simd_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha256_simd_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha256_simd_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 Simd Parity Specification

## Scenarios

### SHA-256 SIMD/scalar parity

#### RFC 6234 §8.5 / FIPS 180-4 §B.1 'abc' — both paths match canonical digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Canonical: ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
val abc_bytes = [0x61, 0x62, 0x63]
val expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
expect(bytes_to_hex(sha256_bytes(abc_bytes))).to_equal(expected)
expect(bytes_to_hex(sha256_bytes_scalar(abc_bytes))).to_equal(expected)
```

</details>

#### 1-byte payload — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _make_n_bytes(1, 0xAA)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 55-byte payload (one-block boundary, no overflow into 2nd block) — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _make_pattern(55)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 56-byte payload (forces 2nd block due to length encoding) — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _make_pattern(56)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 64-byte payload (exact one-block multiple) — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _make_pattern(64)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 1024-byte payload (16 blocks) — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Smaller-than-1KiB-spec workhorse to keep interpreter timing tight.
val msg = _make_pattern(1024)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

#### 2048-byte payload (32 blocks, mixed pattern) — SIMD == scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = _make_pattern(2048)
expect(bytes_to_hex(sha256_bytes(msg))).to_equal(bytes_to_hex(sha256_bytes_scalar(msg)))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/sha256_simd_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-256 SIMD/scalar parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
