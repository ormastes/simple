# Openocd Qemu Arm Specification

> <details>

<!-- sdn-diagram:id=openocd_qemu_arm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openocd_qemu_arm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openocd_qemu_arm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openocd_qemu_arm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Qemu Arm Specification

## Scenarios

### QEMU ARM adapter config

<details>
<summary>Advanced: creates GDB adapter config for QEMU ARM</summary>

#### creates GDB adapter config for QEMU ARM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "test_arm.elf")
expect(cfg.adapter_type).to_equal("gdb")
expect(cfg.port).to_equal(3335)
expect(cfg.architecture).to_equal("arm")
```

</details>


</details>

<details>
<summary>Advanced: uses localhost for QEMU connections</summary>

#### uses localhost for QEMU connections _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "test.elf")
expect(cfg.host).to_equal("localhost")
```

</details>


</details>

<details>
<summary>Advanced: preserves program path</summary>

#### preserves program path _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = AdapterConfig.qemu_arm("localhost", 3335, "/path/to/firmware.elf")
expect(cfg.program).to_equal("/path/to/firmware.elf")
```

</details>


</details>

### QEMU ARM capabilities

<details>
<summary>Advanced: supports memory access</summary>

#### supports memory access _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.supports_memory).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports register access</summary>

#### supports register access _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.supports_registers).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: supports reset</summary>

#### supports reset _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.for_qemu_arm()
expect(caps.can_reset).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/02_integration/baremetal/openocd_qemu_arm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QEMU ARM adapter config
- QEMU ARM capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
