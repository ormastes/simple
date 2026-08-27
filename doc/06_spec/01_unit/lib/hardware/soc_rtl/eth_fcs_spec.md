# Eth Fcs Specification

> <details>

<!-- sdn-diagram:id=eth_fcs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=eth_fcs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

eth_fcs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=eth_fcs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Eth Fcs Specification

## Scenarios

### Ethernet FCS CRC-32 RTL core (IEEE 802.3)

#### computes the canonical check value FCS(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fcs(_digits())).to_equal(0xCBF43926)
```

</details>

#### FCS of the empty frame is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(_fcs(empty)).to_equal(0)
```

</details>

#### FCS of single byte 'A' (0x41) = 0xD3D99E8B

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: [u8] = [0x41u8]
expect(_fcs(a)).to_equal(0xD3D99E8B)
```

</details>

#### distinct frames produce distinct FCS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val other: [u8] = [0x31u8, 0x32u8, 0x33u8, 0x34u8, 0x35u8, 0x36u8, 0x37u8, 0x38u8, 0x30u8]
expect(_fcs(_digits()) == _fcs(other)).to_equal(false)
```

</details>

#### receiver validation accepts a matching recomputed FCS

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_roundtrip()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ethernet FCS CRC-32 RTL core (IEEE 802.3)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
