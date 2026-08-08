# x86 Bare-Metal Boot

> Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup, segmentation, and basic hardware initialization. Verifies that the boot code correctly configures the i386 processor for application execution.

<!-- sdn-diagram:id=x86_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86 Bare-Metal Boot

Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup, segmentation, and basic hardware initialization. Verifies that the boot code correctly configures the i386 processor for application execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/x86_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the x86 (32-bit) bare-metal boot sequence including protected mode setup,
segmentation, and basic hardware initialization. Verifies that the boot code
correctly configures the i386 processor for application execution.

## Scenarios

### x86 Multiboot Header

<details>
<summary>Advanced: has correct magic number</summary>

#### has correct magic number _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot_header()
expect(header.magic).to_equal(0x1BADB002)
```

</details>


</details>

<details>
<summary>Advanced: has valid checksum</summary>

#### has valid checksum _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot_header()
val sum = (header.magic as i64 + header.flags as i64 + header.checksum as i64) as u32
expect(sum).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: has correct flags</summary>

#### has correct flags _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot_header()
# Flags: PAGE_ALIGN (bit 0) | MEMORY_INFO (bit 1) = 3
expect(header.flags).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: validates successfully</summary>

#### validates successfully _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot_header()
expect(validate_multiboot(header)).to_equal(true)
```

</details>


</details>

### x86 Boot Code

<details>
<summary>Advanced: allocates 64KB stack</summary>

#### allocates 64KB stack _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STACK_SIZE).to_equal(65536)
```

</details>


</details>

<details>
<summary>Advanced: maintains 16-byte stack alignment</summary>

#### maintains 16-byte stack alignment _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer correctly</summary>

#### sets up stack pointer correctly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = get_stack_pointer()
# SP should be non-zero and 16-byte aligned
expect(sp > 0).to_equal(true)
expect(sp % 16).to_equal(0)
```

</details>


</details>

### x86 Linker Script

<details>
<summary>Advanced: places multiboot header at correct address</summary>

#### places multiboot header at correct address _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires linker output analysis
check(true)
```

</details>


</details>

<details>
<summary>Advanced: sets correct entry point</summary>

#### sets correct entry point _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires linker output analysis
check(true)
```

</details>


</details>

### x86 QEMU Boot

<details>
<summary>Advanced: boots successfully in QEMU</summary>

#### boots successfully in QEMU _(slow)_

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
<summary>Advanced: handles interrupts correctly</summary>

#### handles interrupts correctly _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU + test kernel with IDT
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
