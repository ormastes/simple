# Replay Vm Types Specification

> <details>

<!-- sdn-diagram:id=replay_vm_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_vm_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_vm_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_vm_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Vm Types Specification

## Scenarios

### VmConfig default_rv32

#### default_rv32 sets arch to RISCV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(128)
val at = cfg.arch.to_text()
expect(at).to_equal("riscv32")
```

</details>

#### default_rv32 sets memory_mb correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(256)
expect(cfg.memory_mb).to_equal(256)
```

</details>

#### default_rv32 sets num_cpus to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(64)
expect(cfg.num_cpus).to_equal(1)
```

</details>

#### default_rv32 replay_mode is Live

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(64)
val mt = cfg.replay_mode.to_text()
expect(mt).to_equal("live")
```

</details>

#### VmReplayMode Record to_text returns record

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = VmReplayMode.Record
expect(m.to_text()).to_equal("record")
```

</details>

#### DeviceIoKind MmioRead to_i32 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = DeviceIoKind.MmioRead
expect(k.to_i32()).to_equal(0)
```

</details>

#### DeviceIoKind Interrupt to_i32 returns 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = DeviceIoKind.Interrupt
expect(k.to_i32()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_vm_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VmConfig default_rv32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
