# Connection Matrix Specification

> <details>

<!-- sdn-diagram:id=connection_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=connection_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

connection_matrix_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=connection_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Connection Matrix Specification

## Scenarios

### ConnectionMatrix default

#### has 8 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
expect(m.count()).to_equal(8)
```

</details>

#### spec 1 is STM32H7 via ST-Link Tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[0]
expect(s.target.to_string()).to_equal("STM32H7")
expect(s.debugger.to_string()).to_equal("ST-Link Tools")
expect(s.stlink_serial).to_equal("002600213137510833333639")
```

</details>

#### spec 2 is STM32H7 via OpenOCD

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[1]
expect(s.target.to_string()).to_equal("STM32H7")
expect(s.debugger.to_string()).to_equal("OpenOCD+GDB")
expect(s.gdb_port).to_equal(3333)
```

</details>

#### spec 5 is T32 Power Debug via T32 Native

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[4]
expect(s.target.to_string()).to_equal("T32 Power Debug")
expect(s.debugger.to_string()).to_equal("T32 Native")
expect(s.t32_port).to_equal(20000)
```

</details>

#### spec 8 is QEMU RV32 via GDB Direct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[7]
expect(s.target.to_string()).to_equal("QEMU RISC-V32")
expect(s.gdb_port).to_equal(1234)
```

</details>

### ConnectionMatrix queries

#### find_by_target STM32H7 returns 2 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_target(DebugTarget.Stm32H7)
expect(result.len()).to_equal(2)
```

</details>

#### find_by_target STM32WB returns 2 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_target(DebugTarget.Stm32Wb)
expect(result.len()).to_equal(2)
```

</details>

#### find_by_target T32PowerDebug returns 2 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_target(DebugTarget.T32PowerDebug)
expect(result.len()).to_equal(2)
```

</details>

#### find_by_target QEMU ARM returns 1 spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_target(DebugTarget.QemuArmCortexM)
expect(result.len()).to_equal(1)
```

</details>

#### find_by_debugger StLinkTools returns 2 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_debugger(DebuggerKind.StLinkTools)
expect(result.len()).to_equal(2)
```

</details>

#### find_by_debugger OpenocdGdb returns 2 specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_debugger(DebuggerKind.OpenocdGdb)
expect(result.len()).to_equal(2)
```

</details>

#### find_by_debugger T32Native returns 1 spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find_by_debugger(DebuggerKind.T32Native)
expect(result.len()).to_equal(1)
```

</details>

#### find specific combo returns correct spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find(DebugTarget.Stm32H7, DebuggerKind.OpenocdGdb)
expect(result != nil).to_equal(true)
```

</details>

#### find unsupported combo returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find(DebugTarget.QemuRiscV32, DebuggerKind.T32Native)
expect(result == nil).to_equal(true)
```

</details>

#### STM32 not connected via T32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val result = m.find(DebugTarget.Stm32H7, DebuggerKind.T32Native)
expect(result == nil).to_equal(true)
```

</details>

### ConnectionSpec properties

#### hardware specs are marked as hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[0]
expect(s.is_hardware()).to_equal(true)
```

</details>

#### T32 Power Debug is marked as hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[4]
expect(s.is_hardware()).to_equal(true)
```

</details>

#### QEMU specs are not hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[6]
expect(s.is_hardware()).to_equal(false)
```

</details>

#### T32 specs are marked as T32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[4]
expect(s.is_t32()).to_equal(true)
```

</details>

#### ST-Link specs are marked as stlink

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[0]
expect(s.is_stlink()).to_equal(true)
```

</details>

#### OpenOCD specs are not T32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConnectionMatrix.default()
val s = m.specs[1]
expect(s.is_t32()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/connection_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ConnectionMatrix default
- ConnectionMatrix queries
- ConnectionSpec properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
