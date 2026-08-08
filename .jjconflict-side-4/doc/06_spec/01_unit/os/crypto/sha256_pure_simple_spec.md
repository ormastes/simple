# Sha256 Pure Simple Specification

> <details>

<!-- sdn-diagram:id=sha256_pure_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha256_pure_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha256_pure_simple_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha256_pure_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 Pure Simple Specification

## Scenarios

### OS pure Simple SHA-256

#### matches RFC 6234 empty-string SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val digest = sha256_with_len(empty, 0)
expect(_bytes_to_hex(digest)).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### matches RFC 6234 abc SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abc: [u8] = [0x61u8, 0x62u8, 0x63u8]
val digest = sha256_with_len(abc, 3)
expect(_bytes_to_hex(digest)).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### matches RFC 4231 HMAC-SHA-256 TC1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x48u8, 0x69u8, 0x20u8, 0x54u8, 0x68u8, 0x65u8, 0x72u8, 0x65u8]
val mac = sha256_hmac_with_len(_hmac_tc1_key(), 20, data, 8)
expect(_bytes_to_hex(mac)).to_equal("b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sha256_pure_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS pure Simple SHA-256

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
