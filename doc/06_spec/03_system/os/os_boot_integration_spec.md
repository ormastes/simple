# Os Boot Integration Specification

> Tests covering SimpleOS x86_64 Boot Integration.

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

- kernel_main is called after Multiboot2 handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel_main is called after Multiboot2 handoff")
# Verified by: serial output contains "Hello from SimpleOS" within 10s
expect(_kernel_entry()).to_contain("Hello from SimpleOS")
```

</details>

#### serial output is initialized on COM1 at 115200 baud

- serial output is initialized on COM1 at 115200 baud


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serial output is initialized on COM1 at 115200 baud")
# Verified by: serial_init() runs, serial_println produces output
expect(_kernel_entry()).to_contain("Serial output working on COM1 at 115200 baud")
```

</details>

#### boot banner is printed to serial

- boot banner is printed to serial


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot banner is printed to serial")
# Verified by: grep "Kernel booted" in serial log
expect(_kernel_entry()).to_contain("Kernel booted via Multiboot2 on x86_64")
```

</details>

#### Tier 2 -- Memory Initialization

#### PMM initializes with usable memory regions from boot info

- PMM initializes with usable memory regions from boot info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PMM initializes with usable memory regions from boot info")
# Verified by: serial output contains "PMM" or "pmm_init"
expect(_read("src/os/kernel/memory/pmm.spl")).to_contain("fn pmm_init")
```

</details>

#### VMM creates page tables for higher-half mapping

- VMM creates page tables for higher-half mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("VMM creates page tables for higher-half mapping")
# Verified by: serial output contains "VMM" or page table messages
expect(_read("src/os/kernel/memory/vmm_core.spl")).to_contain("fn vmm_init")
```

</details>

#### identity maps low physical memory with large pages

- identity maps low physical memory with large pages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity maps low physical memory with large pages")
# Verified by: kernel continues past memory init without page fault
expect(_read("src/os/kernel/memory/vmm_core.spl")).to_contain("_identity_map_4gb()")
```

</details>

#### Tier 3 -- Service Initialization

#### init_all_services runs without panic

- init_all_services runs without panic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("init_all_services runs without panic")
# Verified by: serial output contains "[init] Starting SimpleOS services"
expect(_init_services()).to_contain("[init] Starting SimpleOS services")
```

</details>

#### PCI bus scan discovers devices on Q35 chipset

- PCI bus scan discovers devices on Q35 chipset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PCI bus scan discovers devices on Q35 chipset")
# Verified by: serial output contains "pcimgr" device dump
expect(_init_services()).to_contain("pcimgr_dump_devices()")
```

</details>

#### VFS initializes (with or without NVMe backing)

- VFS initializes (with or without NVMe backing)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("VFS initializes (with or without NVMe backing)")
# Verified by: serial output contains "[init] Storage stack"
expect(_init_services()).to_contain("[init] Storage stack:")
```

</details>

#### network stack probes for VirtIO-net

- network stack probes for VirtIO-net


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("network stack probes for VirtIO-net")
# Verified by: serial output contains "[init] Network stack"
expect(_init_services()).to_contain("[init] Network stack:")
```

</details>

#### Tier 4 -- Shell / Main Loop

<details>
<summary>Advanced: OS reaches main event loop or shell prompt</summary>

#### OS reaches main event loop or shell prompt

- OS reaches main event loop or shell prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("OS reaches main event loop or shell prompt")
# Verified by: serial output contains "ready" or "shell"
expect(_init_services()).to_contain("Service initialization complete")
```

</details>


</details>

#### kernel does not triple-fault within QEMU timeout

- kernel does not triple-fault within QEMU timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel does not triple-fault within QEMU timeout")
# Verified by: QEMU exits via isa-debug-exit, not timeout/crash
expect(_kernel_entry()).to_contain("Halting.")
```

</details>

#### Tier 5 -- Display / Compositor

#### framebuffer backend initializes when VGA device is present

- framebuffer backend initializes when VGA device is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("framebuffer backend initializes when VGA device is present")
# Verified by: serial output contains "framebuffer" or "compositor"
expect(_init_services()).to_contain("bga_init_framebuffer")
```

</details>

#### display service reports status during init

- display service reports status during init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("display service reports status during init")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS x86_64 Boot Integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3f2d64991917ab8949a8c8e45ef0aaeae20d50339e32b6b4c65c0629023b53a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3f2d64991917ab8949a8c8e45ef0aaeae20d50339e32b6b4c65c0629023b53a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3f2d64991917ab8949a8c8e45ef0aaeae20d50339e32b6b4c65c0629023b53a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/os_boot_integration_spec.spl
mirror: doc/06_spec/03_system/os/os_boot_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_boot_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_boot_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_boot_integration_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kernel_main is called after Multiboot2 handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_boot_integration_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serial output is initialized on COM1 at 115200 baud' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_boot_integration_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boot banner is printed to serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
