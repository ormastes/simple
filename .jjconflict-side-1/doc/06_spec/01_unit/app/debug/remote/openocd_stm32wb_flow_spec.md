# Openocd Stm32wb Flow Specification

> <details>

<!-- sdn-diagram:id=openocd_stm32wb_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openocd_stm32wb_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openocd_stm32wb_flow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openocd_stm32wb_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Stm32wb Flow Specification

## Scenarios

### STM32WB OpenOCD config

#### creates config with correct cfg path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32wb("wb_firmware.elf")
expect(s.cfg_path).to_equal("board/stm32wb5x_nucleo.cfg")
```

</details>

#### creates config with GDB port 3334

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32wb("wb_firmware.elf")
expect(s.gdb_port).to_equal(3334)
```

</details>

#### creates config with telnet port 4334

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32wb("wb_firmware.elf")
expect(s.telnet_port).to_equal(4334)
```

</details>

#### target name is STM32WB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32wb("wb_firmware.elf")
expect(s.target_name).to_equal("STM32WB")
```

</details>

### STM32WB OpenOCD flash flow

#### connect then flash succeeds

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
   - Expected: s.flashed is true
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
expect(s.flashed).to_equal(true)
expect(s.state).to_equal("halted")
```

</details>

#### flash without connect fails

1. var s = OpenocdSession for stm32wb
   - Expected: s.flashed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
val result = s.flash("wb_firmware.elf")
expect(s.flashed).to_equal(false)
```

</details>

### STM32WB OpenOCD reset

#### reset_halt transitions to halted

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
4. s resume
5. s reset halt
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
s.resume()
s.reset_halt()
expect(s.state).to_equal("halted")
```

</details>

### STM32WB OpenOCD debug ops

#### halt from running

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
4. s resume
5. s halt
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
s.resume()
s.halt()
expect(s.state).to_equal("halted")
```

</details>

#### resume from halted

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
4. s resume
   - Expected: s.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
s.resume()
expect(s.state).to_equal("running")
```

</details>

#### single step while halted

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
4. s single step
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### set breakpoint

1. var s = OpenocdSession for stm32wb
2. s connect
3. s set breakpoint
4. s set breakpoint
   - Expected: s.breakpoints.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.set_breakpoint("ble_app.c:42")
s.set_breakpoint("ble_app.c:50")
expect(s.breakpoints.len()).to_equal(2)
```

</details>

#### read memory while halted

1. var s = OpenocdSession for stm32wb
2. s connect
3. s flash
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.flash("wb_firmware.elf")
val mem = s.read_memory(0x20000000, 4)
expect(s.state).to_equal("halted")
```

</details>

#### disconnect resets state

1. var s = OpenocdSession for stm32wb
2. s connect
3. s disconnect
   - Expected: s.state equals `disconnected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32wb("wb_firmware.elf")
s.connect()
s.disconnect()
expect(s.state).to_equal("disconnected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/openocd_stm32wb_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- STM32WB OpenOCD config
- STM32WB OpenOCD flash flow
- STM32WB OpenOCD reset
- STM32WB OpenOCD debug ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
