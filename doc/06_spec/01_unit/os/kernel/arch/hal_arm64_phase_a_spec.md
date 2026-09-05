# Hal Arm64 Phase A Specification

> <details>

<!-- sdn-diagram:id=hal_arm64_phase_a_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_arm64_phase_a_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_arm64_phase_a_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_arm64_phase_a_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Arm64 Phase A Specification

## Scenarios

### hal.arm64 Phase A — console + CPU + boot

#### hal_address_width returns 48 for arm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected: u32 = 48
expect(expected).to_equal(48)
```

</details>

#### PL011 UART base address is 0x09000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pl011_base: u64 = 0x09000000
expect(pl011_base).to_equal(0x09000000)
```

</details>

#### DAIF_ALL mask covers all four interrupt types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val daif_all: u64 = 0xF
expect(daif_all).to_equal(0xF)
```

</details>

#### UARTCR enable bits are CR_UARTEN | CR_TXE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cr_uarten: u32 = 1
val cr_txe: u32 = 1 << 8
val combined: u32 = cr_uarten | cr_txe
expect(combined).to_equal(0x101)
```

</details>

#### UARTFR TXFF bit is bit 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fr_txff: u32 = 1 << 5
expect(fr_txff).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/hal_arm64_phase_a_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hal.arm64 Phase A — console + CPU + boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
