# Blake2 Specification

> <details>

<!-- sdn-diagram:id=blake2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake2 Specification

## Scenarios

### BLAKE2b-512 RFC 7693 vectors

#### blake2b_512('') = 786a02f7...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake2b_512_bytes([]))).to_equal(
    "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"
)
```

</details>

#### blake2b_512('abc') = ba80a53f...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake2b_512_bytes(text_to_bytes("abc")))).to_equal(
    "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
)
```

</details>

### BLAKE2b-256 vectors

#### blake2b_256('') = 0e5751c0...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake2b_256_bytes([]))).to_equal(
    "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"
)
```

</details>

#### blake2b_256('abc') = bddd813c...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake2b_256_bytes(text_to_bytes("abc")))).to_equal(
    "bddd813c634239723171ef3fee98579b94964e3bb1cb3e427262c8c068d52319"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/blake2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE2b-512 RFC 7693 vectors
- BLAKE2b-256 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
