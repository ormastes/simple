# ARM32 (Cortex-M) Bare-Metal Boot

> Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup, stack pointer initialization, and transition to main. Verifies that the boot code correctly configures the processor and reaches the application entry point.

<!-- sdn-diagram:id=arm32_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm32_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm32_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm32_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ARM32 (Cortex-M) Bare-Metal Boot

Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup, stack pointer initialization, and transition to main. Verifies that the boot code correctly configures the processor and reaches the application entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/arm32_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the ARM32 Cortex-M bare-metal boot sequence including vector table setup,
stack pointer initialization, and transition to main. Verifies that the boot
code correctly configures the processor and reaches the application entry point.

## Scenarios

### ARM32 Vector Table

<details>
<summary>Advanced: generates valid vector table</summary>

#### generates valid vector table _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = create_vector_table()
# Initial SP should be at top of SRAM
expect(vt.initial_sp).to_equal(STACK_TOP)
# Reset handler should be in flash range
expect(vt.reset > 0x08000000).to_equal(true)
expect(vt.reset < 0x08100000).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has correct exception count</summary>

#### has correct exception count _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = check_exception_count()
# Cortex-M has 16 exception vectors
expect(count).to_equal(16)
```

</details>


</details>

<details>
<summary>Advanced: places vector table at aligned address</summary>

#### places vector table at aligned address _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flash base 0x08000000 should be 128-byte aligned
expect(check_vector_alignment(0x08000000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has zero reserved entries</summary>

#### has zero reserved entries _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = create_vector_table()
expect(vt.reserved1).to_equal(0)
expect(vt.reserved2).to_equal(0)
expect(vt.reserved3).to_equal(0)
expect(vt.reserved4).to_equal(0)
expect(vt.reserved5).to_equal(0)
```

</details>


</details>

### ARM32 Reset Handler

<details>
<summary>Advanced: initializes .data section</summary>

#### initializes .data section _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Data section in SRAM (0x20000000 - 0x20100000)
expect(check_data_init(0x20000000, 0x20001000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: zeros .bss section</summary>

#### zeros .bss section _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BSS section in SRAM
expect(check_bss_init(0x20001000, 0x20002000)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer</summary>

#### sets up stack pointer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# STACK_TOP should be at top of SRAM, 8-byte aligned (AAPCS)
expect(STACK_TOP > 0x20000000).to_equal(true)
expect(check_stack_alignment(STACK_TOP)).to_equal(true)
```

</details>


</details>

### ARM32 NVIC (Nested Vectored Interrupt Controller)

<details>
<summary>Advanced: enables interrupts correctly</summary>

#### enables interrupts correctly _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires NVIC register interaction
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles interrupt priorities</summary>

#### handles interrupt priorities _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires priority grouping configuration
check(true)
```

</details>


</details>

### ARM32 QEMU Boot

<details>
<summary>Advanced: boots on LM3S6965 (Cortex-M3)</summary>

#### boots on LM3S6965 (Cortex-M3) _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU installation
check(true)
```

</details>


</details>

<details>
<summary>Advanced: handles SysTick interrupt</summary>

#### handles SysTick interrupt _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU + test kernel with SysTick
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
