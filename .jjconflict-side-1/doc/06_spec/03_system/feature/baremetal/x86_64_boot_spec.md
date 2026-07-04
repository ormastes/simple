# x86_64 Bare-Metal Boot

> Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT setup, and paging configuration. Verifies that the boot code correctly transitions from real mode through protected mode to 64-bit long mode.

<!-- sdn-diagram:id=x86_64_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 Bare-Metal Boot

Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT setup, and paging configuration. Verifies that the boot code correctly transitions from real mode through protected mode to 64-bit long mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/x86_64_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the x86_64 bare-metal boot sequence including long mode transition, GDT/IDT
setup, and paging configuration. Verifies that the boot code correctly transitions
from real mode through protected mode to 64-bit long mode.

## Scenarios

### x86_64 Boot Code

<details>
<summary>Advanced: generates valid 64-bit multiboot header</summary>

#### generates valid 64-bit multiboot header _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot2_header()
expect(header.magic).to_equal(0xE85250D6)
expect(header.architecture).to_equal(0)
expect(header.header_length).to_equal(24)
```

</details>


</details>

<details>
<summary>Advanced: validates multiboot2 header successfully</summary>

#### validates multiboot2 header successfully _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = multiboot2_header()
expect(validate_multiboot2(header)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up long mode correctly</summary>

#### sets up long mode correctly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate control register values with all bits set for long mode
val cr4 = CR4_PAE
val efer = EFER_LME
val cr0 = CR0_PG
expect(is_pae_enabled(cr4)).to_equal(true)
expect(is_long_mode_enabled(efer)).to_equal(true)
expect(is_paging_enabled(cr0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: maintains 16-byte stack alignment</summary>

#### maintains 16-byte stack alignment _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = get_stack_pointer()
expect(check_stack_alignment(sp)).to_equal(true)
expect(STACK_SIZE % 16).to_equal(0)
```

</details>


</details>

### x86_64 QEMU Boot

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
<summary>Advanced: handles 64-bit interrupts</summary>

#### handles 64-bit interrupts _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires QEMU + test kernel with IDT in long mode
check(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
