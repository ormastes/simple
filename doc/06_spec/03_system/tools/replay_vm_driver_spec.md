# Replay Vm Driver Specification

> <details>

<!-- sdn-diagram:id=replay_vm_driver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_vm_driver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_vm_driver_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_vm_driver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Vm Driver Specification

## Scenarios

### VmConfig default_rv32

#### memory_mb matches requested value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(4)
expect(cfg.memory_mb).to_equal(4)
```

</details>

#### memory_mb is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(4)
expect(cfg.memory_mb).to_be_greater_than(0)
```

</details>

#### num_cpus is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(4)
expect(cfg.num_cpus).to_equal(1)
```

</details>

#### devices list is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(4)
val has_devices = cfg.devices.len() > 0
expect(has_devices).to_equal(true)
```

</details>

### VmReplayDriver create

#### initial state is Stopped

1. var driver = VmReplayDriver create
   - Expected: is_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# memory_mb=0 → 0-byte VirtualMemory, instant allocation
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
val is_stopped = driver.state == VmState.Stopped
expect(is_stopped).to_equal(true)
```

</details>

#### initial cycle_count is zero

1. var driver = VmReplayDriver create
   - Expected: driver.get_cycle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
expect(driver.get_cycle_count()).to_equal(0)
```

</details>

#### initial pc is zero

1. var driver = VmReplayDriver create
   - Expected: driver.get_pc() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
expect(driver.get_pc()).to_equal(0)
```

</details>

### VmReplayDriver start sets Running

#### state is Running after start

1. var driver = VmReplayDriver create
2. driver start
   - Expected: is_running is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0)
val is_running = driver.state == VmState.Running
expect(is_running).to_equal(true)
```

</details>

#### pc equals entry address after start

1. var driver = VmReplayDriver create
2. driver start
   - Expected: driver.get_pc() equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0x1000)
expect(driver.get_pc()).to_equal(0x1000)
```

</details>

### VmReplayDriver step increments cycle

#### step on Stopped driver returns Stopped

1. var driver = VmReplayDriver create
   - Expected: is_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
# state is Stopped — step returns immediately
val result = driver.step()
val is_stopped = result == VmState.Stopped
expect(is_stopped).to_equal(true)
```

</details>

#### cycle_count is greater than zero after one step when Running

1. var driver = VmReplayDriver create
2. driver start
3. driver step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With 0-byte memory, mem_read returns 0.
# Instruction 0x00000000 has opcode 0x00 → unknown → halts.
# CPU still increments cycle_count before returning Stopped.
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0)
driver.step()
expect(driver.get_cycle_count()).to_be_greater_than(0)
```

</details>

### VmReplayDriver save_snapshot returns sequential ids

#### first snapshot id is 0

1. var driver = VmReplayDriver create
   - Expected: id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
val id = driver.save_snapshot()
expect(id).to_equal(0)
```

</details>

#### second snapshot id is 1

1. var driver = VmReplayDriver create
2. driver save snapshot
   - Expected: id2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.save_snapshot()
val id2 = driver.save_snapshot()
expect(id2).to_equal(1)
```

</details>

### VmReplayDriver restore_snapshot

#### restore_snapshot on valid id returns Ok

1. var driver = VmReplayDriver create
2. driver start
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0)
val snap_id = driver.save_snapshot()
val result = driver.restore_snapshot(snap_id)
val is_ok = match result:
    case Ok(_): true
    case Err(_): false
expect(is_ok).to_equal(true)
```

</details>

#### restore_snapshot on missing id returns Err

1. var driver = VmReplayDriver create
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
val result = driver.restore_snapshot(999)
val is_err = match result:
    case Ok(_): false
    case Err(_): true
expect(is_err).to_equal(true)
```

</details>

#### pc is restored to snapshot value

1. var driver = VmReplayDriver create
2. driver start
3. driver start
4. driver restore snapshot
   - Expected: driver.get_pc() equals `0x100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0x100)
val snap_id = driver.save_snapshot()
# Change pc via start, then restore
driver.start(0x200)
driver.restore_snapshot(snap_id)
expect(driver.get_pc()).to_equal(0x100)
```

</details>

### VmReplayDriver run_steps

#### run_steps on Stopped driver stays Stopped

1. var driver = VmReplayDriver create
   - Expected: is_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
val result = driver.run_steps(5)
val is_stopped = result == VmState.Stopped
expect(is_stopped).to_equal(true)
```

</details>

#### run_steps halts on unknown opcode from empty memory

1. var driver = VmReplayDriver create
2. driver start
   - Expected: is_stopped is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mem_read returns 0 → opcode 0x00 → unknown → halts after 1 cycle
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0)
val result = driver.run_steps(100)
val is_stopped = result == VmState.Stopped
expect(is_stopped).to_equal(true)
```

</details>

#### cycle_count is non-zero after run_steps with Running start

1. var driver = VmReplayDriver create
2. driver start
3. driver run steps


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VmConfig.default_rv32(0)
var driver = VmReplayDriver.create(cfg)
driver.start(0)
driver.run_steps(5)
expect(driver.get_cycle_count()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_vm_driver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VmConfig default_rv32
- VmReplayDriver create
- VmReplayDriver start sets Running
- VmReplayDriver step increments cycle
- VmReplayDriver save_snapshot returns sequential ids
- VmReplayDriver restore_snapshot
- VmReplayDriver run_steps

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
