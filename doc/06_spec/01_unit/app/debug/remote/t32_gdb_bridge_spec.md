# T32 Gdb Bridge Specification

> <details>

<!-- sdn-diagram:id=t32_gdb_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_gdb_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_gdb_bridge_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_gdb_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Bridge Specification

## Scenarios

### T32GdbBridgeConfig creation

#### T32 target config has correct T32 port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.t32_port).to_equal(20000)
```

</details>

#### T32 target config has correct GDB port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_port).to_equal(2331)
```

</details>

#### T32 target config has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.target_name).to_equal("T32 Power Debug")
```

</details>

### T32 PRACTICE command formatting

#### GDB server enable command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_enable_cmd()).to_equal("System.Option GDBSERVER ON")
```

</details>

#### GDB server port command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_port_cmd()).to_equal("GDBSERVER.PORT 2331")
```

</details>

#### GDB server disable command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_disable_cmd()).to_equal("System.Option GDBSERVER OFF")
```

</details>

#### PRACTICE DO command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = format_practice_do("t32_startup.cmm")
expect(cmd).to_equal("DO t32_startup.cmm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/t32_gdb_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32GdbBridgeConfig creation
- T32 PRACTICE command formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
