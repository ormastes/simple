# Kmac Specification

> <details>

<!-- sdn-diagram:id=kmac_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kmac_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kmac_spec -> std
kmac_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kmac_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kmac Specification

## Scenarios

### KMAC-128 — NIST SP 800-185 known-answer vectors

#### Sample #1: KMAC128(K, 00010203, 256, \

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = kmac128(_make_key(), _make_data_short(), 256, _empty())
val hex = _bytes_hex(out)
expect(hex.starts_with("e5780b0d")).to_equal(true)
```

</details>

#### Sample #1: KMAC128 output length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = kmac128(_make_key(), _make_data_short(), 256, _empty())
expect(out.len()).to_equal(32)
```

</details>

#### Sample #1: full KMAC128 digest matches NIST vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = kmac128(_make_key(), _make_data_short(), 256, _empty())
expect(_bytes_hex(out)).to_equal("e5780b0d3ea6f7d3a429c5706aa43a00fadbd7d49628839e3187243f456ee14e")
```

</details>

#### Sample #2: KMAC128(K, 00010203, 256, \

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = kmac128(_make_key(), _make_data_short(), 256, _make_custom())
expect(_bytes_hex(out)).to_equal("3b1fba963cd8b0b59e8c1a6d71888b7143651af8ba0a7070c0979e2811324aa5")
```

</details>

#### Sample #3: KMAC128(K, 00..C7, 256, \

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = kmac128(_make_key(), _make_data_200(), 256, _make_custom())
expect(_bytes_hex(out)).to_equal("1f5b4e6cca02209e0dcb5ca635b89a15e271ecc760071dfd805faa38f9729230")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/kmac_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- KMAC-128 — NIST SP 800-185 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
