# Sha224 Kat Specification

> <details>

<!-- sdn-diagram:id=sha224_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha224_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha224_kat_spec -> std
sha224_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha224_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha224 Kat Specification

## Scenarios

### SHA-224 — FIPS 180-4 known-answer vectors

#### SHA-224(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sha224(_empty_bytes()))).to_equal(
    "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f"
)
```

</details>

#### SHA-224(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(sha224(_abc_bytes()))).to_equal(
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7"
)
```

</details>

#### SHA-224 output length is 28 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sha224(_abc_bytes()).len()).to_equal(28)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sha224_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHA-224 — FIPS 180-4 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
