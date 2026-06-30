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
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Bridge Specification

## Scenarios

### T32 GDB bridge repo readiness

#### ships the shared hidden Linux config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.hidden_cfg_path)).to_equal(true)
```

</details>

#### ships both board-specific GDB startup scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.wb_gdb_cmm)).to_equal(true)
expect(rt_file_exists(cfg.h7_gdb_cmm)).to_equal(true)
```

</details>

#### ships the TRACE32 launcher helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.launcher_path)).to_equal(true)
```

</details>

#### ships the GDB enable helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.gdb_enable_path)).to_equal(true)
```

</details>

#### ships the shared STM smoke fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(rt_file_exists(cfg.fixture_asm)).to_equal(true)
expect(rt_file_exists(cfg.fixture_ld)).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
val cmd = cfg.launcher("stm32wb")
expect(cmd.contains("scripts/t32_start_stm.shs")).to_equal(true)
expect(cmd.contains("stm32wb gdb")).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
val cmd = cfg.launcher("stm32h7")
expect(cmd.contains("stm32h7 gdb")).to_equal(true)
```

</details>

#### enable GDB helper command is well-formed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
val cmd = cfg.enable_gdb_server_command()
expect(cmd.contains("scripts/t32_enable_gdb.shs")).to_equal(true)
expect(cmd.contains("20000")).to_equal(true)
expect(cmd.contains("2331")).to_equal(true)
```

</details>

#### GDB target points to the repo default port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
expect(cfg.gdb_target()).to_equal("localhost:2331")
```

</details>

#### t32rem command is well-formed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32GdbConfig.default_config()
val cmd = cfg.t32rem_command("PING")
expect(cmd.contains("t32rem")).to_equal(true)
expect(cmd.contains("PING")).to_equal(true)
expect(cmd.contains("localhost")).to_equal(true)
expect(cmd.contains("port=20000")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/t32_gdb_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 GDB bridge repo readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
