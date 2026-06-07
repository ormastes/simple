# Remote JIT Execution Host-Side Specification

> Comprehensive host-side tests for the remote JIT execution pipeline. These tests verify memory maps, allocators, register helpers, halt instructions, compiler bridge, code uploader, ExecResult, and the baremetal library workload -- all WITHOUT requiring hardware (no QEMU, no OpenOCD, no TRACE32).

<!-- sdn-diagram:id=remote_exec_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_exec_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_exec_host_spec -> std
remote_exec_host_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_exec_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 84 | 84 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote JIT Execution Host-Side Specification

Comprehensive host-side tests for the remote JIT execution pipeline. These tests verify memory maps, allocators, register helpers, halt instructions, compiler bridge, code uploader, ExecResult, and the baremetal library workload -- all WITHOUT requiring hardware (no QEMU, no OpenOCD, no TRACE32).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RJE-001 through #RJE-006 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/remote_jit_impl.md |
| Research | N/A |
| Source | `test/01_unit/lib/remote_exec/remote_exec_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive host-side tests for the remote JIT execution pipeline.
These tests verify memory maps, allocators, register helpers, halt
instructions, compiler bridge, code uploader, ExecResult, and the
baremetal library workload -- all WITHOUT requiring hardware (no QEMU,
no OpenOCD, no TRACE32).

## Key Concepts

| Concept | Description |
|---------|-------------|
| MemoryMap | Target memory layout with code/data regions |
| TargetMemoryAllocator | Bump allocator within a MemoryMap |
| CodeUploader | Uploads machine code bytes via debug protocol |
| CompilerBridge | Compiles Simple source to target bytes |
| ExecResult | Execution outcome (success or failure) |
| ResultCollector | Reads return register after execution |

## Scenarios

### MemoryMap

#### qemu_rv32

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_rv32()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_rv32()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_rv32()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

#### qemu_arm

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_arm()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_arm()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.qemu_arm()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

#### stm32h7 (regression)

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32h7()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32h7()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32h7()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

#### stm32wb

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32wb()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32wb()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.stm32wb()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

#### ch32v307 (regression)

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ch32v307()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ch32v307()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ch32v307()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

#### ghdl_rv32

#### has positive code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ghdl_rv32()
expect(m.code_capacity()).to_be_greater_than(0)
```

</details>

#### has positive data capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ghdl_rv32()
expect(m.data_capacity()).to_be_greater_than(0)
```

</details>

#### stack_top >= data_end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MemoryMap.ghdl_rv32()
val ok = m.stack_top >= m.data_end
expect(ok).to_equal(true)
```

</details>

### TargetMemoryAllocator

#### allocation basics

#### returns address within code region

1. var alloc = TargetMemoryAllocator new
   - Expected: in_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = TargetMemoryAllocator.new(MemoryMap.qemu_rv32())
val result = alloc.allocate(64, 4)
val addr = result.ok.unwrap()
val m = MemoryMap.qemu_rv32()
val in_range = addr >= m.code_start and addr < m.code_end
expect(in_range).to_equal(true)
```

</details>

#### respects alignment

1. var alloc = TargetMemoryAllocator new
   - Expected: aligned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = TargetMemoryAllocator.new(MemoryMap.qemu_rv32())
val result = alloc.allocate(16, 16)
val addr = result.ok.unwrap()
val aligned = (addr % 16) == 0
expect(aligned).to_equal(true)
```

</details>

#### fails when memory exhausted

1. var alloc = TargetMemoryAllocator new
   - Expected: first.is_ok() is true
   - Expected: second.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val small_map = MemoryMap(
    code_start: 0x1000,
    code_end: 0x1040,
    data_start: 0x1040,
    data_end: 0x1080,
    stack_top: 0x1080,
    allow_expand: false
)
var alloc = TargetMemoryAllocator.new(small_map)
# Allocate all 64 bytes
val first = alloc.allocate(64, 4)
expect(first.is_ok()).to_equal(true)
# Next allocation should fail
val second = alloc.allocate(1, 1)
expect(second.is_err()).to_equal(true)
```

</details>

#### tracking

#### remaining decreases after allocation

1. var alloc = TargetMemoryAllocator new
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = TargetMemoryAllocator.new(MemoryMap.qemu_rv32())
val before = alloc.remaining()
val result = alloc.allocate(256, 4)
expect(result.is_ok()).to_equal(true)
val after = alloc.remaining()
expect(after).to_be_less_than(before)
```

</details>

#### allocation_count tracks allocations

1. var alloc = TargetMemoryAllocator new
   - Expected: alloc.allocation_count() equals `0`
   - Expected: alloc.allocation_count() equals `1`
   - Expected: alloc.allocation_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = TargetMemoryAllocator.new(MemoryMap.qemu_rv32())
expect(alloc.allocation_count()).to_equal(0)
val r1 = alloc.allocate(32, 4)
expect(alloc.allocation_count()).to_equal(1)
val r2 = alloc.allocate(32, 4)
expect(alloc.allocation_count()).to_equal(2)
```

</details>

#### reset frees all memory

1. var alloc = TargetMemoryAllocator new
2. alloc reset
   - Expected: alloc.remaining() equals `full_remaining`
   - Expected: alloc.allocation_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = TargetMemoryAllocator.new(MemoryMap.qemu_rv32())
val full_remaining = alloc.remaining()
val r1 = alloc.allocate(128, 4)
expect(alloc.remaining()).to_be_less_than(full_remaining)
alloc.reset()
expect(alloc.remaining()).to_equal(full_remaining)
expect(alloc.allocation_count()).to_equal(0)
```

</details>

### Register Names

#### arm_reg_name

#### returns r0 for register 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_reg_name(0)).to_equal("r0")
```

</details>

#### returns sp for register 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_reg_name(13)).to_equal("sp")
```

</details>

#### returns lr for register 14

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_reg_name(14)).to_equal("lr")
```

</details>

#### returns pc for register 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_reg_name(15)).to_equal("pc")
```

</details>

#### covers mid-range registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_reg_name(7)).to_equal("r7")
expect(arm_reg_name(12)).to_equal("r12")
```

</details>

#### rv32_reg_name

#### returns zero for register 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(0)).to_equal("zero")
```

</details>

#### returns ra for register 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(1)).to_equal("ra")
```

</details>

#### returns sp for register 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(2)).to_equal("sp")
```

</details>

#### returns a0 for register 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(10)).to_equal("a0")
```

</details>

#### returns a7 for register 17

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(17)).to_equal("a7")
```

</details>

#### returns t6 for register 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(31)).to_equal("t6")
```

</details>

#### returns pc for register 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(32)).to_equal("pc")
```

</details>

#### returns s0 for register 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_reg_name(8)).to_equal("s0")
```

</details>

#### reg_name_for_arch dispatch

#### dispatches ARM32 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reg_name_for_arch(13, Architecture.Arm32)).to_equal("sp")
```

</details>

#### dispatches RiscV32 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reg_name_for_arch(10, Architecture.RiscV32)).to_equal("a0")
```

</details>

#### returns rv32 name for unknown architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reg_name_for_arch(2, Architecture.X86_64)).to_equal("sp")
```

</details>

### Halt Instructions

#### halt_instruction_for

#### returns EBREAK for RiscV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(halt_instruction_for(Architecture.RiscV32)).to_equal(EBREAK_RV32)
```

</details>

#### returns BKPT for Arm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(halt_instruction_for(Architecture.Arm32)).to_equal(BKPT_ARM)
```

</details>

#### EBREAK_RV32 is 0x00100073

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EBREAK_RV32).to_equal(0x00100073)
```

</details>

#### BKPT_ARM is 0xBE00

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BKPT_ARM).to_equal(0xBE00)
```

</details>

#### halt_instruction_size

#### Arm32 halt is 2 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(halt_instruction_size(Architecture.Arm32)).to_equal(2)
```

</details>

#### RiscV32 halt is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(halt_instruction_size(Architecture.RiscV32)).to_equal(4)
```

</details>

### Register Indices

#### RiscV32

#### pc is register 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pc_register_index(Architecture.RiscV32)).to_equal(32)
```

</details>

#### sp is register 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sp_register_index(Architecture.RiscV32)).to_equal(2)
```

</details>

#### return register is a0 (10)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(return_register_index(Architecture.RiscV32)).to_equal(10)
```

</details>

#### link register is ra (1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(link_register_index(Architecture.RiscV32)).to_equal(1)
```

</details>

#### has 8 argument registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = arg_register_indices(Architecture.RiscV32)
expect(args.len()).to_equal(8)
```

</details>

#### max args is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_args(Architecture.RiscV32)).to_equal(8)
```

</details>

#### Arm32

#### pc is register 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pc_register_index(Architecture.Arm32)).to_equal(15)
```

</details>

#### sp is register 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sp_register_index(Architecture.Arm32)).to_equal(13)
```

</details>

#### return register is r0 (0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(return_register_index(Architecture.Arm32)).to_equal(0)
```

</details>

#### link register is lr (14)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(link_register_index(Architecture.Arm32)).to_equal(14)
```

</details>

#### has 4 argument registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = arg_register_indices(Architecture.Arm32)
expect(args.len()).to_equal(4)
```

</details>

#### max args is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(max_args(Architecture.Arm32)).to_equal(4)
```

</details>

### CompilerBridge

#### Arm32

#### returns Ok with bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CompilerBridge.compile("val x = 0", Architecture.Arm32, 0x40010000)
expect(result.is_ok()).to_equal(true)
```

</details>

#### produces non-empty byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CompilerBridge.compile("val x = 0", Architecture.Arm32, 0x40010000)
val bytes = result.ok.unwrap()
expect(bytes.len()).to_be_greater_than(0)
```

</details>

#### RiscV32

#### returns Ok with bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CompilerBridge.compile("val x = 0", Architecture.RiscV32, 0x80010000)
expect(result.is_ok()).to_equal(true)
```

</details>

#### produces non-empty byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CompilerBridge.compile("val x = 0", Architecture.RiscV32, 0x80010000)
val bytes = result.ok.unwrap()
expect(bytes.len()).to_be_greater_than(0)
```

</details>

#### unsupported architecture

#### returns Err for X86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = CompilerBridge.compile("val x = 0", Architecture.X86_64, 0x1000)
expect(result.is_err()).to_equal(true)
```

</details>

#### compile_remote_binary function

#### Arm32 returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compile_remote_binary("val x = 0", Architecture.Arm32, 0x40010000)
expect(result.is_ok()).to_equal(true)
```

</details>

#### RiscV32 returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compile_remote_binary("val x = 0", Architecture.RiscV32, 0x80010000)
expect(result.is_ok()).to_equal(true)
```

</details>

### CodeUploader

#### upload

#### rejects empty buffer

1. mock read ok factory
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_bytes: [i32] = []
val result = CodeUploader.upload(
    "test",
    empty_bytes,
    0x80010000,
    mock_write_ok,
    mock_read_ok_factory([])
)
expect(result.is_err()).to_equal(true)
```

</details>

#### succeeds with mock write and read

1. mock read ok factory
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0x13, 0x05, 0x00, 0x00]
val result = CodeUploader.upload(
    "test_code",
    bytes,
    0x80010000,
    mock_write_ok,
    mock_read_ok_factory(bytes)
)
expect(result.is_ok()).to_equal(true)
```

</details>

#### returns CodeInfo with correct name

1. mock read ok factory
   - Expected: info.name equals `my_func`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0x13, 0x05, 0x00, 0x00]
val result = CodeUploader.upload(
    "my_func",
    bytes,
    0x80010000,
    mock_write_ok,
    mock_read_ok_factory(bytes)
)
val info = result.ok.unwrap()
expect(info.name).to_equal("my_func")
```

</details>

#### returns CodeInfo with correct address

1. mock read ok factory
   - Expected: info.addr equals `0x80010000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0x13, 0x05, 0x00, 0x00]
val result = CodeUploader.upload(
    "my_func",
    bytes,
    0x80010000,
    mock_write_ok,
    mock_read_ok_factory(bytes)
)
val info = result.ok.unwrap()
expect(info.addr).to_equal(0x80010000)
```

</details>

#### returns CodeInfo with correct size

1. mock read ok factory
   - Expected: info.size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0x13, 0x05, 0x00, 0x00]
val result = CodeUploader.upload(
    "my_func",
    bytes,
    0x80010000,
    mock_write_ok,
    mock_read_ok_factory(bytes)
)
val info = result.ok.unwrap()
expect(info.size).to_equal(4)
```

</details>

#### verify

#### detects byte mismatch

1. mock read ok factory
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected: [i32] = [0x13, 0x05, 0x00, 0x00]
val corrupted: [i32] = [0x13, 0xFF, 0x00, 0x00]
val result = CodeUploader.verify(
    0x80010000,
    expected,
    mock_read_ok_factory(corrupted)
)
expect(result.is_err()).to_equal(true)
```

</details>

#### succeeds when bytes match

1. mock read ok factory
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0xAA, 0xBB, 0xCC, 0xDD]
val result = CodeUploader.verify(
    0x80010000,
    bytes,
    mock_read_ok_factory(bytes)
)
expect(result.is_ok()).to_equal(true)
```

</details>

#### fails when read returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [0x13, 0x05]
val result = CodeUploader.verify(
    0x80010000,
    bytes,
    mock_read_err
)
expect(result.is_err()).to_equal(true)
```

</details>

### ExecResult

#### success

#### is_ok returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.success(42, 100, "breakpoint")
expect(r.is_ok()).to_equal(true)
```

</details>

#### stores return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.success(42, 100, "breakpoint")
expect(r.return_value).to_equal(42)
```

</details>

#### stores duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.success(0, 250, "halt")
expect(r.duration_ms).to_equal(250)
```

</details>

#### stores halt reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.success(0, 0, "breakpoint")
expect(r.halt_reason).to_equal("breakpoint")
```

</details>

#### has empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.success(0, 0, "halt")
expect(r.error).to_equal("")
```

</details>

#### failure

#### is_ok returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.failure("timeout")
expect(r.is_ok()).to_equal(false)
```

</details>

#### stores error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.failure("connection lost")
expect(r.error).to_equal("connection lost")
```

</details>

#### has zero return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ExecResult.failure("error")
expect(r.return_value).to_equal(0)
```

</details>

### ResultCollector

#### collect with mock

#### reads return register and builds success

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val collector = ResultCollector.new(
    Architecture.RiscV32,
    mock_read_register_42
)
val result = collector.collect("breakpoint", 50)
expect(result.is_ok()).to_equal(true)
val exec = result.ok.unwrap()
expect(exec.return_value).to_equal(42)
expect(exec.duration_ms).to_equal(50)
```

</details>

#### propagates read error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val collector = ResultCollector.new(
    Architecture.Arm32,
    mock_read_register_err
)
val result = collector.collect("halt", 0)
expect(result.is_err()).to_equal(true)
```

</details>

### Baremetal Library Workload

#### host execution

#### returns 0 indicating all checks pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_baremetal_library_workload()
expect(result).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 84 |
| Active scenarios | 84 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/remote_jit_impl.md](doc/05_design/remote_jit_impl.md)


</details>
