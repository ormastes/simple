# Stm32h7 Openocd Specification

> <details>

<!-- sdn-diagram:id=stm32h7_openocd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32h7_openocd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32h7_openocd_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32h7_openocd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stm32h7 Openocd Specification

## Scenarios

### STM32H7 OpenOCD repo readiness

#### uses the expected ST-LINK interface config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = OpenocdH7Config.default_config()
expect(cfg.interface_cfg).to_equal("interface/stlink.cfg")
```

</details>

#### uses the expected STM32H7 target config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = OpenocdH7Config.default_config()
expect(cfg.target_cfg).to_equal("target/stm32h7x.cfg")
```

</details>

#### uses the expected ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = OpenocdH7Config.default_config()
expect(cfg.gdb_port).to_equal(3333)
expect(cfg.telnet_port).to_equal(4333)
```

</details>

#### ships the shared STM smoke fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = OpenocdH7Config.default_config()
expect(rt_file_exists(cfg.fixture_asm)).to_equal(true)
expect(rt_file_exists(cfg.fixture_ld)).to_equal(true)
```

</details>

#### launch command is well-formed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = OpenocdH7Config.default_config()
val cmd = cfg.launch_command()
expect(cmd.contains("openocd")).to_equal(true)
expect(cmd.contains("interface/stlink.cfg")).to_equal(true)
expect(cmd.contains("target/stm32h7x.cfg")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/stm32h7_openocd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- STM32H7 OpenOCD repo readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
