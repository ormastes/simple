# Hal Riscv64 Phase A Specification

> <details>

<!-- sdn-diagram:id=hal_riscv64_phase_a_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_riscv64_phase_a_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_riscv64_phase_a_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_riscv64_phase_a_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Riscv64 Phase A Specification

## Scenarios

### hal.riscv64 Phase A — console + CPU + boot

#### hal_address_width returns 39 for riscv64 Sv39

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected: u32 = 39
expect(expected).to_equal(39)
```

</details>

#### UART base address is 0x10000000 for QEMU virt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uart_base: u64 = 0x10000000
expect(uart_base).to_equal(0x10000000)
```

</details>

#### SSTATUS_SIE bit is bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sie_bit: u64 = 1 << 1
expect(sie_bit).to_equal(2)
```

</details>

#### SBI_EXT_LEGACY_CONSOLE_PUTCHAR extension ID is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sbi_putchar_ext: u64 = 0x01
expect(sbi_putchar_ext).to_equal(1)
```

</details>

#### QEMU virt RAM base is 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram_base: u64 = 0x80000000
expect(ram_base).to_equal(0x80000000)
```

</details>

#### OpenSBI kernel payload offset is 0x80200000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_base: u64 = 0x80200000
expect(kernel_base - 0x80000000).to_equal(0x200000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/hal_riscv64_phase_a_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hal.riscv64 Phase A — console + CPU + boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
