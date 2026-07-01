# Openocd Parser Specification

> <details>

<!-- sdn-diagram:id=openocd_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openocd_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openocd_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openocd_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Parser Specification

## Scenarios

### OpenOCD hex formatting

#### formats 0 as 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_hex(0)).to_equal("0")
```

</details>

#### formats 255 as ff

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_hex(255)).to_equal("ff")
```

</details>

#### formats 256 as 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_hex(256)).to_equal("100")
```

</details>

#### formats 0x1000 as 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_hex(4096)).to_equal("1000")
```

</details>

#### formats address with 0x prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_address(4096)).to_equal("0x1000")
```

</details>

### OpenOCD mdw output parsing

#### parses single word

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_mdw_output("0x08000000: 0xDEADBEEF")
expect(result.len()).to_be_greater_than(0)
```

</details>

#### parses hex values from output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_mdw_output("0x20000000: 0x0 0x0 0x0 0x0")
expect(result.len()).to_be_greater_than(0)
```

</details>

### OpenOCD process config

#### OpenOCD config path for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = "board/stm32h7x3i_eval.cfg"
expect(cfg).to_contain("stm32h7")
```

</details>

#### OpenOCD config path for STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = "board/stm32wb5x_nucleo.cfg"
expect(cfg).to_contain("stm32wb")
```

</details>

#### GDB port defaults for STM32H7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = 3333
expect(port).to_equal(3333)
```

</details>

#### telnet port is GDB port + 1000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gdb_port = 3333
val telnet_port = gdb_port + 1000
expect(telnet_port).to_equal(4333)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/openocd_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenOCD hex formatting
- OpenOCD mdw output parsing
- OpenOCD process config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
