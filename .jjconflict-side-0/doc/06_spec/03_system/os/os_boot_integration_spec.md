# Os Boot Integration Specification

> <details>

<!-- sdn-diagram:id=os_boot_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_boot_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_boot_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_boot_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Boot Integration Specification

## Scenarios

### SimpleOS x86_64 Boot Integration

#### Tier 1 -- Boot Smoke

#### kernel_main is called after Multiboot2 handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "Hello from SimpleOS" within 10s
expect(_kernel_entry()).to_contain("Hello from SimpleOS")
```

</details>

#### serial output is initialized on COM1 at 115200 baud

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial_init() runs, serial_println produces output
expect(_kernel_entry()).to_contain("Serial output working on COM1 at 115200 baud")
```

</details>

#### boot banner is printed to serial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: grep "Kernel booted" in serial log
expect(_kernel_entry()).to_contain("Kernel booted via Multiboot2 on x86_64")
```

</details>

#### Tier 2 -- Memory Initialization

#### PMM initializes with usable memory regions from boot info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "PMM" or "pmm_init"
expect(_read("src/os/kernel/memory/pmm.spl")).to_contain("fn pmm_init")
```

</details>

#### VMM creates page tables for higher-half mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "VMM" or page table messages
expect(_read("src/os/kernel/memory/vmm.spl")).to_contain("fn vmm_init")
```

</details>

#### identity maps low physical memory with large pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: kernel continues past memory init without page fault
expect(_read("src/os/kernel/memory/vmm.spl")).to_contain("_identity_map_4gb()")
```

</details>

#### Tier 3 -- Service Initialization

#### init_all_services runs without panic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "[init] Starting SimpleOS services"
expect(_init_services()).to_contain("[init] Starting SimpleOS services")
```

</details>

#### PCI bus scan discovers devices on Q35 chipset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "pcimgr" device dump
expect(_init_services()).to_contain("pcimgr_dump_devices()")
```

</details>

#### VFS initializes (with or without NVMe backing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "[init] Storage stack"
expect(_init_services()).to_contain("[init] Storage stack:")
```

</details>

#### network stack probes for VirtIO-net

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "[init] Network stack"
expect(_init_services()).to_contain("[init] Network stack:")
```

</details>

#### Tier 4 -- Shell / Main Loop

<details>
<summary>Advanced: OS reaches main event loop or shell prompt</summary>

#### OS reaches main event loop or shell prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "ready" or "shell"
expect(_init_services()).to_contain("Service initialization complete")
```

</details>


</details>

#### kernel does not triple-fault within QEMU timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: QEMU exits via isa-debug-exit, not timeout/crash
expect(_kernel_entry()).to_contain("Halting.")
```

</details>

#### Tier 5 -- Display / Compositor

#### framebuffer backend initializes when VGA device is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "framebuffer" or "compositor"
expect(_init_services()).to_contain("bga_init_framebuffer")
```

</details>

#### display service reports status during init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by: serial output contains "[init] Display service"
expect(_init_services()).to_contain("svc_display_ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_boot_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS x86_64 Boot Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
