# Blake3 Specification

> <details>

<!-- sdn-diagram:id=blake3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blake3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blake3_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blake3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blake3 Specification

## Scenarios

### BLAKE3 official test vectors

#### blake3('') = af1349b9...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake3_bytes([]))).to_equal(
    "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
)
```

</details>

#### blake3('abc') = 6437b3ac...

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_hex(blake3_bytes(text_to_bytes("abc")))).to_equal(
    "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/blake3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BLAKE3 official test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
