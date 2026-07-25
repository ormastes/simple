# Serpent Specification

> <details>

<!-- sdn-diagram:id=serpent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serpent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serpent_spec -> std
serpent_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serpent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serpent Specification

## Scenarios

### Serpent KAT

#### enc zero/zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(serpent_encrypt_block(_zero16(), _zero16()))).to_equal("3620b17ae6a993d09618b8768266bae9")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/serpent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Serpent KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
