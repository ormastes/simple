# Gdt Layout Specification

> <details>

<!-- sdn-diagram:id=gdt_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gdt_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gdt_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gdt_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gdt Layout Specification

## Scenarios

### kernel.arch.x86_64 GDT selector layout

#### kernel selectors are 8 bytes apart

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(kernel_ds - kernel_cs).to_equal(8)
```

</details>

#### user CS 32-bit immediately follows kernel DS

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(user_cs_32 - kernel_ds).to_equal(8)
```

</details>

#### user DS is 8 bytes after user CS 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(user_ds - user_cs_32).to_equal(8)
```

</details>

#### user CS 64-bit is 16 bytes after user CS 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(user_cs_64 - user_cs_32).to_equal(16)
```

</details>

#### GDT spans 6 descriptors (48 bytes), limit is 47

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gdt_size: u64 = user_cs_64 + 8
expect(gdt_size).to_equal(48)
expect(gdt_size - 1).to_equal(47)
```

</details>

#### MSR_STAR kernel field matches kernel_cs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msr_star_kernel_field: u64 = kernel_cs
expect(msr_star_kernel_field).to_equal(0x08)
```

</details>

#### MSR_STAR user field matches user_cs_32 or'd with RPL 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msr_star_user_field: u64 = user_cs_32 | 3
expect(msr_star_user_field).to_equal(0x1B)
# Verify derived SYSRET 64-bit CS = 0x2B
expect(msr_star_user_field + 16).to_equal(0x2B)
# Verify derived SYSRET SS = 0x23
expect(msr_star_user_field + 8).to_equal(0x23)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/gdt_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel.arch.x86_64 GDT selector layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
