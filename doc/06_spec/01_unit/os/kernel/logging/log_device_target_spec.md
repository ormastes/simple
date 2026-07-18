# Log Device Target Specification

> <details>

<!-- sdn-diagram:id=log_device_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=log_device_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

log_device_target_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=log_device_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Device Target Specification

## Scenarios

### log level constants ordering

#### orders TRACE through OFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LOG_TRACE).to_equal(0)
expect(LOG_DEBUG).to_equal(1)
expect(LOG_INFO).to_equal(2)
expect(LOG_WARN).to_equal(3)
expect(LOG_ERROR).to_equal(4)
expect(LOG_FATAL).to_equal(5)
expect(LOG_OFF).to_equal(6)
```

</details>

#### names each level via log_level_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_name(LOG_TRACE)).to_equal("TRACE")
expect(log_level_name(LOG_DEBUG)).to_equal("DEBUG")
expect(log_level_name(LOG_INFO)).to_equal("INFO")
expect(log_level_name(LOG_WARN)).to_equal("WARN")
expect(log_level_name(LOG_ERROR)).to_equal("ERROR")
expect(log_level_name(LOG_FATAL)).to_equal("FATAL")
```

</details>

### log target bit constants

#### assigns DEVICE=1, SEMIHOST=2, HOST_FILE=4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TARGET_DEVICE).to_equal(1)
expect(TARGET_SEMIHOST).to_equal(2)
expect(TARGET_HOST_FILE).to_equal(4)
```

</details>

### log_kind_from_text translates profile serial-kind to runtime code

#### com1 → LOG_DEV_KIND_COM1 (1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_kind_from_text("com1")).to_equal(LOG_DEV_KIND_COM1)
expect(log_kind_from_text("com1")).to_equal(1)
```

</details>

#### pl011 → LOG_DEV_KIND_PL011 (2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_kind_from_text("pl011")).to_equal(LOG_DEV_KIND_PL011)
expect(log_kind_from_text("pl011")).to_equal(2)
```

</details>

#### ns16550 → LOG_DEV_KIND_NS16550 (3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_kind_from_text("ns16550")).to_equal(LOG_DEV_KIND_NS16550)
expect(log_kind_from_text("ns16550")).to_equal(3)
```

</details>

#### unknown text → 0 (sentinel: no device dispatch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_kind_from_text("nonsense")).to_equal(0)
expect(log_kind_from_text("")).to_equal(0)
```

</details>

### log_parse_level: SIMPLE_LOG-style level token parsing

#### parses canonical lowercase tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_parse_level("trace")).to_equal(LOG_TRACE)
expect(log_parse_level("debug")).to_equal(LOG_DEBUG)
expect(log_parse_level("info")).to_equal(LOG_INFO)
expect(log_parse_level("warn")).to_equal(LOG_WARN)
expect(log_parse_level("error")).to_equal(LOG_ERROR)
expect(log_parse_level("fatal")).to_equal(LOG_FATAL)
expect(log_parse_level("off")).to_equal(LOG_OFF)
```

</details>

#### unknown tokens default to LOG_INFO

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_parse_level("verbose")).to_equal(LOG_INFO)
expect(log_parse_level("")).to_equal(LOG_INFO)
```

</details>

### log_parse_targets: comma-separated target list to bitmask

#### parses single targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_parse_targets("serial")).to_equal(1)
expect(log_parse_targets("device")).to_equal(1)
expect(log_parse_targets("semihost")).to_equal(2)
expect(log_parse_targets("file")).to_equal(4)
```

</details>

#### ORs multiple targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_parse_targets("serial,semihost")).to_equal(3)
expect(log_parse_targets("serial,semihost,file")).to_equal(7)
```

</details>

#### empty string → 0 (no targets)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_parse_targets("")).to_equal(0)
```

</details>

### platform target exposes serial config per arch

#### x86_64 platform → com1 @ 0x3F8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if val platform = simpleos_platform_target_by_name("x86_64"):
    expect(platform.qemu_serial_kind).to_equal("com1")
    expect(platform.qemu_serial_base).to_equal(0x3F8u64)
```

</details>

#### arm64 platform → pl011 @ 0x09000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if val platform = simpleos_platform_target_by_name("arm64"):
    expect(platform.qemu_serial_kind).to_equal("pl011")
    expect(platform.qemu_serial_base).to_equal(0x09000000u64)
```

</details>

#### riscv64 platform → ns16550 @ 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if val platform = simpleos_platform_target_by_name("riscv64"):
    expect(platform.qemu_serial_kind).to_equal("ns16550")
    expect(platform.qemu_serial_base).to_equal(0x10000000u64)
```

</details>

### MachineProfile mirrors the platform's serial config

#### riscv64 MachineProfile carries ns16550 @ 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = riscv64_machine_profile()
expect(profile.qemu_serial_kind).to_equal("ns16550")
expect(profile.qemu_serial_base).to_equal(0x10000000u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/logging/log_device_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- log level constants ordering
- log target bit constants
- log_kind_from_text translates profile serial-kind to runtime code
- log_parse_level: SIMPLE_LOG-style level token parsing
- log_parse_targets: comma-separated target list to bitmask
- platform target exposes serial config per arch
- MachineProfile mirrors the platform's serial config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
