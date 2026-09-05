# Replay Rv32i Vm Specification

> 1. var cpu = Rv32iCpu create

<!-- sdn-diagram:id=replay_rv32i_vm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_rv32i_vm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_rv32i_vm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_rv32i_vm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Rv32i Vm Specification

## Scenarios

### Rv32iCpu initial state

#### pc is zero after create

1. var cpu = Rv32iCpu create
   - Expected: cpu.pc equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
expect(cpu.pc).to_equal(0)
```

</details>

#### cycle_count is zero after create

1. var cpu = Rv32iCpu create
   - Expected: cpu.cycle_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
expect(cpu.cycle_count).to_equal(0)
```

</details>

#### x0 is zero after create

1. var cpu = Rv32iCpu create
   - Expected: cpu.read_register(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
expect(cpu.read_register(0)).to_equal(0)
```

</details>

### Rv32iCpu write and read register

#### read_register returns written value

1. var cpu = Rv32iCpu create
2. cpu write register
   - Expected: cpu.read_register(1) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.write_register(1, 42)
expect(cpu.read_register(1)).to_equal(42)
```

</details>

#### write to x1 does not affect x2

1. var cpu = Rv32iCpu create
2. cpu write register
   - Expected: cpu.read_register(2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.write_register(1, 42)
expect(cpu.read_register(2)).to_equal(0)
```

</details>

#### write_register masks to 32 bits

1. var cpu = Rv32iCpu create
2. cpu write register
   - Expected: cpu.read_register(1) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
# 0x1_FFFF_FFFF masked to 0xFFFF_FFFF
cpu.write_register(1, 0x1FFFFFFFF)
expect(cpu.read_register(1)).to_equal(0xFFFFFFFF)
```

</details>

### Rv32iCpu x0 always zero

#### x0 stays zero after write attempt

1. var cpu = Rv32iCpu create
2. cpu write register
   - Expected: cpu.read_register(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.write_register(0, 999)
expect(cpu.read_register(0)).to_equal(0)
```

</details>

### Rv32iCpu set_pc and get_pc

#### get_pc returns value set by set_pc

1. var cpu = Rv32iCpu create
2. cpu set pc
   - Expected: cpu.get_pc() equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.set_pc(0x1000)
expect(cpu.get_pc()).to_equal(0x1000)
```

</details>

#### set_pc to zero returns zero

1. var cpu = Rv32iCpu create
2. cpu set pc
3. cpu set pc
   - Expected: cpu.get_pc() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.set_pc(0x1000)
cpu.set_pc(0)
expect(cpu.get_pc()).to_equal(0)
```

</details>

### Rv32iCpu read_all_registers

#### result contains x0

1. var cpu = Rv32iCpu create
   - Expected: has_x0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
val regs = cpu.read_all_registers()
val has_x0 = regs.contains_key("x0")
expect(has_x0).to_equal(true)
```

</details>

#### result contains x31

1. var cpu = Rv32iCpu create
   - Expected: has_x31 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
val regs = cpu.read_all_registers()
val has_x31 = regs.contains_key("x31")
expect(has_x31).to_equal(true)
```

</details>

#### result contains pc key

1. var cpu = Rv32iCpu create
   - Expected: has_pc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
val regs = cpu.read_all_registers()
val has_pc = regs.contains_key("pc")
expect(has_pc).to_equal(true)
```

</details>

#### x0 value in map is zero

1. var cpu = Rv32iCpu create
   - Expected: x0_val equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
val regs = cpu.read_all_registers()
val x0_val = regs.get("x0") ?? -1
expect(x0_val).to_equal(0)
```

</details>

#### written register appears in map

1. var cpu = Rv32iCpu create
2. cpu write register
   - Expected: x5_val equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Rv32iCpu.create()
cpu.write_register(5, 99)
val regs = cpu.read_all_registers()
val x5_val = regs.get("x5") ?? -1
expect(x5_val).to_equal(99)
```

</details>

### VirtualMemory create

#### size field matches requested size

1. var mem = VirtualMemory create
   - Expected: mem.size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
expect(mem.size).to_equal(4096)
```

</details>

#### page_size field matches requested page_size

1. var mem = VirtualMemory create
   - Expected: mem.page_size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
expect(mem.page_size).to_equal(4096)
```

</details>

#### all bytes are zero after create

1. var mem = VirtualMemory create
   - Expected: mem.read(0, 1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(64, 64)
expect(mem.read(0, 1)).to_equal(0)
```

</details>

### VirtualMemory write and read byte

#### read back matches written byte

1. var mem = VirtualMemory create
2. mem write
   - Expected: mem.read(0, 1) equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0x42, 1)
expect(mem.read(0, 1)).to_equal(0x42)
```

</details>

#### write at offset 10 reads back correctly

1. var mem = VirtualMemory create
2. mem write
   - Expected: mem.read(10, 1) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(10, 0xFF, 1)
expect(mem.read(10, 1)).to_equal(0xFF)
```

</details>

#### byte is masked to 8 bits

1. var mem = VirtualMemory create
2. mem write
   - Expected: mem.read(0, 1) equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0x1AB, 1)
expect(mem.read(0, 1)).to_equal(0xAB)
```

</details>

### VirtualMemory write and read word

#### little-endian 32-bit write reads back same value

1. var mem = VirtualMemory create
2. mem write
   - Expected: mem.read(0, 4) equals `3735928559`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
# 0xDEADBEEF in i64 (positive): 3735928559
mem.write(0, 3735928559, 4)
expect(mem.read(0, 4)).to_equal(3735928559)
```

</details>

#### 16-bit write reads back same value

1. var mem = VirtualMemory create
2. mem write
   - Expected: mem.read(0, 2) equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0xABCD, 2)
expect(mem.read(0, 2)).to_equal(0xABCD)
```

</details>

#### word write does not corrupt adjacent byte

1. var mem = VirtualMemory create
2. mem write
3. mem write
   - Expected: mem.read(4, 1) equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0xAABBCCDD, 4)
mem.write(4, 0x42, 1)
expect(mem.read(4, 1)).to_equal(0x42)
```

</details>

### VirtualMemory dirty tracking

#### dirty_page_count is zero before any write

1. var mem = VirtualMemory create
   - Expected: mem.dirty_page_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
expect(mem.dirty_page_count()).to_equal(0)
```

</details>

#### dirty_page_count greater than zero after write

1. var mem = VirtualMemory create
2. mem write


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0x42, 1)
expect(mem.dirty_page_count()).to_be_greater_than(0)
```

</details>

#### clear_dirty resets dirty_page_count to zero

1. var mem = VirtualMemory create
2. mem write
3. mem clear dirty
   - Expected: mem.dirty_page_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0x42, 1)
mem.clear_dirty()
expect(mem.dirty_page_count()).to_equal(0)
```

</details>

#### data survives clear_dirty

1. var mem = VirtualMemory create
2. mem write
3. mem clear dirty
   - Expected: mem.read(0, 1) equals `0x77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.write(0, 0x77, 1)
mem.clear_dirty()
expect(mem.read(0, 1)).to_equal(0x77)
```

</details>

### VirtualMemory load_binary

#### first byte matches after load

1. var mem = VirtualMemory create
2. mem load binary
   - Expected: mem.read(0, 1) equals `0x42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.load_binary(0, [0x42, 0x43, 0x44])
expect(mem.read(0, 1)).to_equal(0x42)
```

</details>

#### second byte matches after load

1. var mem = VirtualMemory create
2. mem load binary
   - Expected: mem.read(1, 1) equals `0x43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.load_binary(0, [0x42, 0x43, 0x44])
expect(mem.read(1, 1)).to_equal(0x43)
```

</details>

#### third byte matches after load

1. var mem = VirtualMemory create
2. mem load binary
   - Expected: mem.read(2, 1) equals `0x44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.load_binary(0, [0x42, 0x43, 0x44])
expect(mem.read(2, 1)).to_equal(0x44)
```

</details>

#### load at non-zero base address

1. var mem = VirtualMemory create
2. mem load binary
   - Expected: mem.read(100, 1) equals `0xAA`
   - Expected: mem.read(101, 1) equals `0xBB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = VirtualMemory.create(4096, 4096)
mem.load_binary(100, [0xAA, 0xBB])
expect(mem.read(100, 1)).to_equal(0xAA)
expect(mem.read(101, 1)).to_equal(0xBB)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_rv32i_vm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Rv32iCpu initial state
- Rv32iCpu write and read register
- Rv32iCpu x0 always zero
- Rv32iCpu set_pc and get_pc
- Rv32iCpu read_all_registers
- VirtualMemory create
- VirtualMemory write and read byte
- VirtualMemory write and read word
- VirtualMemory dirty tracking
- VirtualMemory load_binary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
