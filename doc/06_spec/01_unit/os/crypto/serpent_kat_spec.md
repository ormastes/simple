# Serpent Kat Specification

> <details>

<!-- sdn-diagram:id=serpent_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serpent_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serpent_kat_spec -> std
serpent_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serpent_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serpent Kat Specification

## Scenarios

### Serpent KAT

#### enc zero/zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_enc_zero()).to_equal("3620b17ae6a993d09618b8768266bae9")
```

</details>

#### ct is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_enc_zero_len()).to_equal(16)
```

</details>

#### rt zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_rt_zero()).to_equal("00000000000000000000000000000000")
```

</details>

#### dec vec1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_dec_vec1()).to_equal("00000000000000000000000000000000")
```

</details>

#### enc vec2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_enc_vec2()).to_equal("b2288b968ae8b08648d1ce9606fd992d")
```

</details>

#### dec vec2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_dec_vec2()).to_equal("d29d576fcea3a3a7ed9099f29273d78e")
```

</details>

#### enc vec3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_enc_vec3()).to_equal("264e5481eff42a4606abda06c0bfda3d")
```

</details>

#### dec vec3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_dec_vec3()).to_equal("00000000000000000000000000000000")
```

</details>

#### rt 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_t_rt_256()).to_equal("00000000000000000000000000000000")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/serpent_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Serpent KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
