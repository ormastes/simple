# Blake3 Kat Specification

> <details>

<!-- sdn-diagram:id=blake3_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake3_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake3_kat_spec -> std
blake3_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake3_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake3 Kat Specification

## Scenarios

### BLAKE3 KAT — V1: input_len=0

#### V1 hash(empty) = af1349b9...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3(_v1_input()))).to_equal(
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
)
```

</details>

#### V1 keyed_hash(empty) = 92b2b756...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3_keyed(_make_key(), _v1_input()))).to_equal(
    "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26"
)
```

</details>

#### V1 derive_key(empty) = 2cc39783...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3_kdf(_make_context(), _v1_input()))).to_equal(
    "2cc39783c223154fea8dfb7c1b1660f2ac2dcbd1c1de8277b0b0dd39b7e50d7d"
)
```

</details>

### BLAKE3 KAT — V2: input_len=1

#### V2 hash([0x00]) = 2d3adedff1...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3(_v2_input()))).to_equal(
    "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"
)
```

</details>

### BLAKE3 KAT — V3: input_len=63

#### V3 hash(63 bytes) = e9bc37a5...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3(_v3_input()))).to_equal(
    "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b"
)
```

</details>

### BLAKE3 KAT — V4: input_len=1024

#### V4 hash(1024 bytes) = 42214739...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(blake3(_v4_input()))).to_equal(
    "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/blake3_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE3 KAT — V1: input_len=0
- BLAKE3 KAT — V2: input_len=1
- BLAKE3 KAT — V3: input_len=63
- BLAKE3 KAT — V4: input_len=1024

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
