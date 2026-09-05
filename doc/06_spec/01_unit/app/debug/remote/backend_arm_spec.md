# Backend Arm Specification

> <details>

<!-- sdn-diagram:id=backend_arm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_arm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_arm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_arm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Arm Specification

## Scenarios

### RemoteArmBackend factory methods

#### openocd_stm32h7 has openocd connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.openocd_stm32h7()
expect(info.has_openocd).to_equal(true)
expect(info.has_gdb).to_equal(false)
expect(info.has_t32).to_equal(false)
```

</details>

#### openocd_stm32h7 targets Cortex-M7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.openocd_stm32h7()
expect(info.target_core).to_equal("Cortex-M7")
```

</details>

#### openocd_stm32wb targets Cortex-M4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.openocd_stm32wb()
expect(info.target_core).to_equal("Cortex-M4")
```

</details>

#### trace32_native has t32 connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.trace32_native()
expect(info.has_t32).to_equal(true)
expect(info.has_openocd).to_equal(false)
```

</details>

#### trace32_gdb_bridge has t32_gdb connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.trace32_gdb_bridge()
expect(info.has_t32_gdb).to_equal(true)
expect(info.has_t32).to_equal(false)
```

</details>

#### gdb_only has gdb connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = ArmBackendInfo.gdb_only()
expect(info.has_gdb).to_equal(true)
expect(info.has_openocd).to_equal(false)
```

</details>

### RemoteArmBackend naming

#### all backends report remote-arm name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ArmBackendInfo.openocd_stm32h7().name).to_equal("remote-arm")
expect(ArmBackendInfo.trace32_native().name).to_equal("remote-arm")
expect(ArmBackendInfo.gdb_only().name).to_equal("remote-arm")
```

</details>

#### backend name is distinct from remote-riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm_name = "remote-arm"
val rv_name = "remote-riscv32"
expect(arm_name != rv_name).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/backend_arm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RemoteArmBackend factory methods
- RemoteArmBackend naming

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
