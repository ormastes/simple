# T32 Native Flow Specification

> <details>

<!-- sdn-diagram:id=t32_native_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_native_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_native_flow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_native_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Native Flow Specification

## Scenarios

### T32 Power Debug T32 Native config

#### has correct T32 config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32NativeSession.for_t32_target()
expect(s.t32_cfg).to_equal("t32_startup.cmm")
```

</details>

#### has T32 port 20000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32NativeSession.for_t32_target()
expect(s.t32_port).to_equal(20000)
```

</details>

#### target name is T32 Power Debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = T32NativeSession.for_t32_target()
expect(s.target_name).to_equal("T32 Power Debug")
```

</details>

### T32 Power Debug T32 Native flash and reset

#### connect then flash succeeds

1. var s = T32NativeSession for t32 target
2. s connect
3. s flash program
   - Expected: s.flashed is true
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("target_app.elf")
expect(s.flashed).to_equal(true)
expect(s.state).to_equal("halted")
```

</details>

#### system reset transitions to halted

1. var s = T32NativeSession for t32 target
2. s connect
3. s system reset
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.system_reset()
expect(s.state).to_equal("halted")
```

</details>

#### flash without connect fails

1. var s = T32NativeSession for t32 target
   - Expected: s.flashed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
val result = s.flash_program("app.elf")
expect(s.flashed).to_equal(false)
```

</details>

### T32 Power Debug T32 Native trace and coverage

#### trace capture returns trace data

1. var s = T32NativeSession for t32 target
2. s connect
3. s trace capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.trace_capture(500)
expect(s.trace_data).to_contain("Trace.Arm")
expect(s.trace_data).to_contain("500ms")
```

</details>

#### coverage collect returns coverage data

1. var s = T32NativeSession for t32 target
2. s connect
3. s coverage collect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.coverage_collect("main")
expect(s.coverage_data).to_contain("COVerage.ListFunc")
expect(s.coverage_data).to_contain("main")
```

</details>

#### trace capture when disconnected fails

1. var s = T32NativeSession for t32 target
   - Expected: s.trace_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
val result = s.trace_capture(1000)
expect(s.trace_data).to_equal("")
```

</details>

### T32 Power Debug T32 Native debug ops

#### halt from running

1. var s = T32NativeSession for t32 target
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
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.resume()
s.halt()
expect(s.state).to_equal("halted")
```

</details>

#### resume from halted

1. var s = T32NativeSession for t32 target
2. s connect
3. s flash program
4. s resume
   - Expected: s.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.resume()
expect(s.state).to_equal("running")
```

</details>

#### single step while halted

1. var s = T32NativeSession for t32 target
2. s connect
3. s flash program
4. s single step
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### read memory while halted

1. var s = T32NativeSession for t32 target
2. s connect
3. s flash program
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
val mem = s.read_memory(0x08000000, 16)
expect(s.state).to_equal("halted")
```

</details>

#### read register while halted

1. var s = T32NativeSession for t32 target
2. s connect
3. s flash program
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
val reg = s.read_register("pc")
expect(s.state).to_equal("halted")
```

</details>

#### set breakpoint

1. var s = T32NativeSession for t32 target
2. s connect
3. s set breakpoint
   - Expected: s.state equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = T32NativeSession.for_t32_target()
s.connect()
s.set_breakpoint("main\\10")
expect(s.state).to_equal("connected")
```

</details>

#### full debug cycle: flash -> resume -> halt -> step

1. var s = T32NativeSession for t32 target
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
var s = T32NativeSession.for_t32_target()
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/t32_native_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Power Debug T32 Native config
- T32 Power Debug T32 Native flash and reset
- T32 Power Debug T32 Native trace and coverage
- T32 Power Debug T32 Native debug ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
