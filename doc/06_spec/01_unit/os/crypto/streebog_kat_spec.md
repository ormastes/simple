# Streebog Kat Specification

> <details>

<!-- sdn-diagram:id=streebog_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=streebog_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

streebog_kat_spec -> std
streebog_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=streebog_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Streebog Kat Specification

## Scenarios

### Streebog-512 — RFC 6986 GOST R 34.11-2012 known-answer vectors

#### Streebog-512(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(streebog_512(_empty_bytes()))).to_equal(
    "8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a"
)
```

</details>

#### Streebog-512(M1) = 1b54d01a... (63-byte ASCII digit string)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(streebog_512(_m1_bytes()))).to_equal(
    "1b54d01a4af5b9d5cc3d86d68d285462b19abc2475222f35c085122be4ba1ffa00ad30f8767b3a82384c6574f024c311e2a481332b08ef7f41797891c1646f48"
)
```

</details>

#### Streebog-512 digest length is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(streebog_512(_empty_bytes()).len()).to_equal(64)
```

</details>

#### Streebog-512(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "8e945da209aa869f0455928529bcae4679e9873ab707b55315f56ceb98bef0a7362f715528356ee83cda5f2aac4c6ad2ba3a715c1bcd81cb8e9f90bf4c1c1a8a"
expect(_bytes_hex(streebog_512(_empty_bytes())) == _reverse_hex_pairs(expected)).to_equal(false)
```

</details>

### Streebog-256 — RFC 6986 GOST R 34.11-2012 known-answer vectors

#### Streebog-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(streebog_256(_empty_bytes()))).to_equal(
    "3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb"
)
```

</details>

#### Streebog-256 digest length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(streebog_256(_empty_bytes()).len()).to_equal(32)
```

</details>

#### Streebog-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "3f539a213e97c802cc229d474c6aa32a825a360b2a933a949fd925208d9ce1bb"
expect(_bytes_hex(streebog_256(_empty_bytes())) == _reverse_hex_pairs(expected)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/streebog_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Streebog-512 — RFC 6986 GOST R 34.11-2012 known-answer vectors
- Streebog-256 — RFC 6986 GOST R 34.11-2012 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
