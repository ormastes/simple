# T32 Native Specification

> <details>

<!-- sdn-diagram:id=t32_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_native_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Native Specification

## Scenarios

### T32 native repo readiness

#### uses the installed t32rem path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
expect(cfg.t32rem_path).to_equal("/opt/t32/bin/pc_linux64/t32rem")
```

</details>

#### ships the shared hidden Linux config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.hidden_cfg_path)).to_equal(true)
```

</details>

#### ships the TRACE32 launcher helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.launcher_path)).to_equal(true)
```

</details>

#### ships both board-specific native startup scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.wb_native_cmm)).to_equal(true)
expect(rt_file_exists(cfg.h7_native_cmm)).to_equal(true)
```

</details>

#### requires the Lauterbach startup scripts already present on host

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
expect(rt_file_exists(cfg.wb_startup_path)).to_equal(true)
expect(rt_file_exists(cfg.h7_startup_path)).to_equal(true)
```

</details>

#### ships the shared STM smoke fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
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
val cfg = T32Config.default_config()
val cmd = cfg.launcher("stm32wb")
expect(cmd.contains("scripts/t32_start_stm.shs")).to_equal(true)
expect(cmd.contains("stm32wb native")).to_equal(true)
```

</details>

#### launcher command is well-formed for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
val cmd = cfg.launcher("stm32h7")
expect(cmd.contains("stm32h7 native")).to_equal(true)
```

</details>

#### remote API ping command is well-formed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
val cmd = cfg.ping_command()
expect(cmd.contains("t32rem")).to_equal(true)
expect(cmd.contains("PING")).to_equal(true)
expect(cmd.contains("localhost")).to_equal(true)
expect(cmd.contains("port=20000")).to_equal(true)
```

</details>

#### system up command is well-formed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32Config.default_config()
val cmd = cfg.system_up_command()
expect(cmd.contains("SYStem.Up")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/t32_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 native repo readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
