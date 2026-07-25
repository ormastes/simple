# Openocd Stm32h7 Flow Specification

> <details>

<!-- sdn-diagram:id=openocd_stm32h7_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=openocd_stm32h7_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

openocd_stm32h7_flow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=openocd_stm32h7_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Openocd Stm32h7 Flow Specification

## Scenarios

### STM32H7 OpenOCD config

#### creates config with correct cfg path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32h7("firmware.elf")
expect(s.cfg_path).to_equal("board/stm32h7x3i_eval.cfg")
```

</details>

#### creates config with GDB port 3333

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32h7("firmware.elf")
expect(s.gdb_port).to_equal(3333)
```

</details>

#### creates config with telnet port 4333

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32h7("firmware.elf")
expect(s.telnet_port).to_equal(4333)
```

</details>

#### starts disconnected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = OpenocdSession.for_stm32h7("firmware.elf")
expect(s.state).to_equal("disconnected")
```

</details>

### STM32H7 OpenOCD flash flow

#### connect then flash succeeds

1. var s = OpenocdSession for stm32h7
2. s connect
   - Expected: s.flashed is true
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
val result = s.flash("firmware.elf")
expect(s.flashed).to_equal(true)
expect(s.state).to_equal("halted")
```

</details>

#### flash without connect fails

1. var s = OpenocdSession for stm32h7
   - Expected: s.flashed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
val result = s.flash("firmware.elf")
expect(s.flashed).to_equal(false)
```

</details>

#### flash then reset_run transitions to running

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
4. s reset run
   - Expected: s.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
s.reset_run()
expect(s.state).to_equal("running")
```

</details>

### STM32H7 OpenOCD reset flow

#### reset_halt from running transitions to halted

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
4. s reset run
5. s reset halt
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
s.reset_run()
s.reset_halt()
expect(s.state).to_equal("halted")
```

</details>

#### reset_halt when disconnected fails

1. var s = OpenocdSession for stm32h7
   - Expected: s.state equals `disconnected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
val result = s.reset_halt()
expect(s.state).to_equal("disconnected")
```

</details>

### STM32H7 OpenOCD debug ops

#### halt from running succeeds

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
4. s reset run
5. s halt
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
s.reset_run()
s.halt()
expect(s.state).to_equal("halted")
```

</details>

#### resume from halted succeeds

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
4. s resume
   - Expected: s.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
s.resume()
expect(s.state).to_equal("running")
```

</details>

#### single step while halted succeeds

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
4. s single step
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### set breakpoint while connected

1. var s = OpenocdSession for stm32h7
2. s connect
3. s set breakpoint
   - Expected: s.breakpoints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.set_breakpoint("main.c:10")
expect(s.breakpoints.len()).to_equal(1)
```

</details>

#### read memory while halted

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
val mem = s.read_memory(0x08000000, 4)
expect(s.state).to_equal("halted")
```

</details>

#### read register while halted

1. var s = OpenocdSession for stm32h7
2. s connect
3. s flash
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.flash("firmware.elf")
val reg = s.read_register("r0")
expect(s.state).to_equal("halted")
```

</details>

### STM32H7 OpenOCD monitor

#### send monitor command

1. var s = OpenocdSession for stm32h7
2. s connect
3. s monitor
   - Expected: s.last_monitor_cmd equals `mdw 0x08000000 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
s.connect()
s.monitor("mdw 0x08000000 4")
expect(s.last_monitor_cmd).to_equal("mdw 0x08000000 4")
```

</details>

#### monitor when disconnected fails

1. var s = OpenocdSession for stm32h7
   - Expected: s.state equals `disconnected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = OpenocdSession.for_stm32h7("firmware.elf")
val result = s.monitor("reset halt")
expect(s.state).to_equal("disconnected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/openocd_stm32h7_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- STM32H7 OpenOCD config
- STM32H7 OpenOCD flash flow
- STM32H7 OpenOCD reset flow
- STM32H7 OpenOCD debug ops
- STM32H7 OpenOCD monitor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
