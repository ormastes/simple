# T32 Gdb Bridge Flow Specification

> <details>

<!-- sdn-diagram:id=t32_gdb_bridge_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_gdb_bridge_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_gdb_bridge_flow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_gdb_bridge_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Bridge Flow Specification

## Scenarios

### T32 Power Debug GDB Bridge config

#### has T32 port 20000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
expect(s.t32_port).to_equal(20000)
```

</details>

#### has GDB port 2331

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
expect(s.gdb_port).to_equal(2331)
```

</details>

#### has correct T32 config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
expect(s.t32_cfg).to_equal("t32_startup.cmm")
```

</details>

#### target name is T32 Power Debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
expect(s.target_name).to_equal("T32 Power Debug")
```

</details>

### T32 Power Debug GDB Bridge connection

#### full connect enables GDB server and connects GDB

1. var s = T32GdbSession for t32 target
2. s connect
   - Expected: s.state equals `connected`
   - Expected: s.gdb_server_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
expect(s.state).to_equal("connected")
expect(s.gdb_server_enabled).to_equal(true)
```

</details>

#### connect without t32rem fails GDB server

1. var s = T32GdbSession for t32 target
   - Expected: s.gdb_server_enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
val result = s.enable_gdb_server()
expect(s.gdb_server_enabled).to_equal(false)
```

</details>

### T32 Power Debug GDB Bridge flash and reset

#### flash via PRACTICE

1. var s = T32GdbSession for t32 target
2. s connect
3. s flash program
   - Expected: s.flashed is true
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.flash_program("target_app.elf")
expect(s.flashed).to_equal(true)
expect(s.state).to_equal("halted")
```

</details>

#### system reset via PRACTICE

1. var s = T32GdbSession for t32 target
2. s connect
3. s system reset
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.system_reset()
expect(s.state).to_equal("halted")
```

</details>

### T32 Power Debug GDB Bridge trace and coverage

#### trace capture via PRACTICE

1. s connect
2. s trace capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
s.connect()
s.trace_capture(500)
expect(s.trace_data).to_contain("ETM trace")
expect(s.trace_data).to_contain("500ms")
```

</details>

#### coverage collect via PRACTICE

1. s connect
2. s coverage collect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32GdbSession.for_t32_target()
s.connect()
s.coverage_collect("main")
expect(s.coverage_data).to_contain("Coverage main")
expect(s.coverage_data).to_contain("85%")
```

</details>

#### trace when disconnected fails

1. var s = T32GdbSession for t32 target
   - Expected: s.trace_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
val result = s.trace_capture(1000)
expect(s.trace_data).to_equal("")
```

</details>

### T32 Power Debug GDB Bridge practice script

#### run practice script

1. var s = T32GdbSession for t32 target
2. s connect
3. s practice script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.practice_script("t32_startup.cmm")
expect(s.practice_result).to_contain("DO t32_startup.cmm completed")
```

</details>

#### practice script when disconnected fails

1. var s = T32GdbSession for t32 target
   - Expected: s.practice_result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
val result = s.practice_script("test.cmm")
expect(s.practice_result).to_equal("")
```

</details>

### T32 Power Debug GDB Bridge debug ops via GDB

#### halt via GDB

1. var s = T32GdbSession for t32 target
2. s connect
3. s flash program
4. s resume
5. s halt
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.resume()
s.halt()
expect(s.state).to_equal("halted")
```

</details>

#### single step via GDB

1. var s = T32GdbSession for t32 target
2. s connect
3. s flash program
4. s single step
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### set breakpoint via GDB

1. var s = T32GdbSession for t32 target
2. s connect
3. s set breakpoint
   - Expected: s.breakpoints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.set_breakpoint("main.c:10")
expect(s.breakpoints.len()).to_equal(1)
```

</details>

#### read memory via GDB while halted

1. var s = T32GdbSession for t32 target
2. s connect
3. s flash program
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
val mem = s.read_memory(0x08000000, 4)
expect(s.state).to_equal("halted")
```

</details>

#### full debug cycle: flash -> resume -> halt -> step

1. var s = T32GdbSession for t32 target
2. s connect
3. s flash program
   - Expected: s.state equals `halted`
4. s resume
   - Expected: s.state equals `running`
5. s halt
   - Expected: s.state equals `halted`
6. s single step
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
s.flash_program("target_app.elf")
expect(s.state).to_equal("halted")
s.resume()
expect(s.state).to_equal("running")
s.halt()
expect(s.state).to_equal("halted")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### disconnect disables GDB server

1. var s = T32GdbSession for t32 target
2. s connect
   - Expected: s.gdb_server_enabled is true
3. s disconnect
   - Expected: s.gdb_server_enabled is false
   - Expected: s.state equals `disconnected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32GdbSession.for_t32_target()
s.connect()
expect(s.gdb_server_enabled).to_equal(true)
s.disconnect()
expect(s.gdb_server_enabled).to_equal(false)
expect(s.state).to_equal("disconnected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/t32_gdb_bridge_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Power Debug GDB Bridge config
- T32 Power Debug GDB Bridge connection
- T32 Power Debug GDB Bridge flash and reset
- T32 Power Debug GDB Bridge trace and coverage
- T32 Power Debug GDB Bridge practice script
- T32 Power Debug GDB Bridge debug ops via GDB

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
