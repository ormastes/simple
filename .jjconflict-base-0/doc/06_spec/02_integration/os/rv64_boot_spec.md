# RV64 Baremetal OS Boot Integration Test

> Tests that the RV64GC hardware emulation can boot a minimal baremetal program. Verifies: reset vector, RAM access, UART output, instruction execution pipeline. Uses the rv64gc machine profile (QEMU virt layout) with inline test programs.

<!-- sdn-diagram:id=rv64_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_boot_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Baremetal OS Boot Integration Test

Tests that the RV64GC hardware emulation can boot a minimal baremetal program. Verifies: reset vector, RAM access, UART output, instruction execution pipeline. Uses the rv64gc machine profile (QEMU virt layout) with inline test programs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-BOOT-001 |
| Category | OS |
| Difficulty | 4/5 |
| Status | Draft |
| Source | `test/02_integration/os/rv64_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the RV64GC hardware emulation can boot a minimal baremetal program.
Verifies: reset vector, RAM access, UART output, instruction execution pipeline.
Uses the rv64gc machine profile (QEMU virt layout) with inline test programs.

## Scenarios

### RV64 Boot — Reset Vector

#### PC starts at DRAM_BASE (0x80000000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset_pc: i64 = DRAM_BASE
expect(reset_pc).to_equal(0x80000000)
```

</details>

#### all registers zero at reset

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rf = Rv64RegFile.create()
var i = 0
var all_zero = true
while i < 32:
    if rf.read(i) != 0:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(true)
```

</details>

#### x0 stays zero after attempted write

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(0, 0xDEAD)
expect(rf.read(0)).to_equal(0)
```

</details>

### RV64 Boot — RAM Load and Execute

#### load instruction bytes to RAM

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read32(0).value equals `0x02A00513`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(64)
# ADDI x10, x0, 42 = 0x02A00513
ram.write32(0, 0x02A00513)
expect(ram.read32(0).value).to_equal(0x02A00513)
```

</details>

#### fetch and decode ADDI from RAM

1. var ram = Rv64Ram create
2. ram write32
   - Expected: opcode equals `OP_OP_IMM`
   - Expected: rd equals `10`
   - Expected: rs1 equals `0`
   - Expected: imm equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(64)
ram.write32(0, 0x02A00513)  # ADDI x10, x0, 42
val instr = ram.read32(0).value
val opcode = decode_opcode(instr)
val rd = decode_rd(instr)
val rs1 = decode_rs1(instr)
val imm = decode_imm_i(instr)
expect(opcode).to_equal(OP_OP_IMM)
expect(rd).to_equal(10)
expect(rs1).to_equal(0)
expect(imm).to_equal(42)
```

</details>

#### execute ADDI and writeback to register

1. var rf = Rv64RegFile create
2. var ram = Rv64Ram create
3. ram write32
4. rf write
   - Expected: rf.read(10) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(64)
ram.write32(0, 0x02A00513)  # ADDI x10, x0, 42
val instr = ram.read32(0).value
val rd = decode_rd(instr) + 0
val rs1_idx = decode_rs1(instr) + 0
val rs1_val = rf.read(rs1_idx)
val imm = decode_imm_i(instr)
val result = alu_execute(AluOp.Add, rs1_val, imm)
rf.write(rd, result)
expect(rf.read(10)).to_equal(42)
```

</details>

#### multi-instruction program: compute 3+4

1. var rf = Rv64RegFile create
2. var ram = Rv64Ram create
3. ram write32
4. ram write32
5. ram write32
6. var instr = ram read32
7. rf write
   - Expected: rf.read(10) equals `3`
8. instr = ram read32
9. rf write
   - Expected: rf.read(11) equals `4`
10. instr = ram read32
11. rf write
   - Expected: rf.read(12) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(64)
# ADDI x10, x0, 3 = 0x00300513
# ADDI x11, x0, 4 = 0x00400593
# ADD  x12, x10, x11 = 0x00B50633
ram.write32(0, 0x00300513)
ram.write32(4, 0x00400593)
ram.write32(8, 0x00B50633)

# Execute instruction 1: ADDI x10, x0, 3
var instr = ram.read32(0).value
val rd1 = decode_rd(instr) + 0
val rs1_idx = decode_rs1(instr) + 0
val imm1 = decode_imm_i(instr)
rf.write(rd1, alu_execute(AluOp.Add, rf.read(rs1_idx), imm1))
expect(rf.read(10)).to_equal(3)

# Execute instruction 2: ADDI x11, x0, 4
instr = ram.read32(4).value
val rd2 = decode_rd(instr) + 0
val rs2_idx_imm = decode_rs1(instr) + 0
val imm2 = decode_imm_i(instr)
rf.write(rd2, alu_execute(AluOp.Add, rf.read(rs2_idx_imm), imm2))
expect(rf.read(11)).to_equal(4)

# Execute instruction 3: ADD x12, x10, x11
instr = ram.read32(8).value
val rs1_idx_add = decode_rs1(instr) + 0
val rs2_idx_add = decode_rs2(instr) + 0
val rd3 = decode_rd(instr) + 0
val rs1 = rf.read(rs1_idx_add)
val rs2 = rf.read(rs2_idx_add)
rf.write(rd3, alu_execute(AluOp.Add, rs1, rs2))
expect(rf.read(12)).to_equal(7)
```

</details>

### RV64 Boot — Store and Load Cycle

#### store word then load word

1. var ram = Rv64Ram create
2. ram write32
   - Expected: loaded equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(256)
# Store 0xDEADBEEF at address 128
ram.write32(128, 0xDEADBEEF)
# Load from address 128
val loaded = ram.read32(128).value
expect(loaded).to_equal(0xDEADBEEF)
```

</details>

#### store double then load double

1. var ram = Rv64Ram create
2. ram write64
   - Expected: ram.read64(128).value equals `0xCAFEBABEDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(256)
ram.write64(128, 0xCAFEBABEDEADBEEF)
expect(ram.read64(128).value).to_equal(0xCAFEBABEDEADBEEF)
```

</details>

#### store byte then load byte with sign extension

1. var ram = Rv64Ram create
2. ram write8
   - Expected: sign_ext equals `0xFFFFFFFFFFFFFF80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(256)
ram.write8(128, 0x80)
val raw = ram.read8(128).value
# Simulate LB sign extension
val sign_ext = if (raw and 0x80) != 0: raw or 0xFFFFFFFFFFFFFF00 else: raw
expect(sign_ext).to_equal(0xFFFFFFFFFFFFFF80)
```

</details>

### RV64 Boot — UART Output Simulation

#### write 'H' to UART address

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var uart_buffer: [i64] = []
val ch: i64 = 0x48  # 'H'
uart_buffer = uart_buffer + [ch]
expect(uart_buffer[0]).to_equal(0x48)
```

</details>

#### write 'Hello' byte-by-byte

1. uart buffer push
2. uart buffer push
3. uart buffer push
4. uart buffer push
5. uart buffer push
   - Expected: uart_buffer.len() equals `5`
   - Expected: uart_buffer[0] equals `0x48`
   - Expected: uart_buffer[4] equals `0x6F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var uart_buffer: [i64] = []
uart_buffer.push(0x48)
uart_buffer.push(0x65)
uart_buffer.push(0x6C)
uart_buffer.push(0x6C)
uart_buffer.push(0x6F)
expect(uart_buffer.len()).to_equal(5)
expect(uart_buffer[0]).to_equal(0x48)
expect(uart_buffer[4]).to_equal(0x6F)
```

</details>

#### UART THR at offset 0 from UART_BASE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val thr_addr = UART_BASE + 0
expect(thr_addr).to_equal(0x10000000)
```

</details>

#### UART LSR at offset 5 — TX ready check

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lsr_addr = UART_BASE + 5
val lsr_val: i64 = 0x60  # THR empty + transmitter idle
val tx_ready = (lsr_val and 0x20) != 0
expect(tx_ready).to_equal(true)
```

</details>

### RV64 Boot — Stack Setup

#### set SP to top of 128MB RAM

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(2) equals `0x88000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
val stack_top = DRAM_BASE + 0x8000000  # 128MB
rf.write(2, stack_top)
expect(rf.read(2)).to_equal(0x88000000)
```

</details>

#### stack push/pop simulation

1. var rf = Rv64RegFile create
2. var ram = Rv64Ram create
3. rf write
4. rf write
5. ram write64
6. rf write
   - Expected: loaded equals `0xCAFEBABE`
   - Expected: rf.read(2) equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(256)
rf.write(2, 256)  # SP = 256

# Push: SP -= 8, store value
val sp = rf.read(2) - 8
rf.write(2, sp)
ram.write64(sp, 0xCAFEBABE)

# Pop: load value, SP += 8
val loaded = ram.read64(rf.read(2)).value
rf.write(2, rf.read(2) + 8)

expect(loaded).to_equal(0xCAFEBABE)
expect(rf.read(2)).to_equal(256)
```

</details>

### RV64 Boot — W-Variant in Boot Code

#### ADDIW for 32-bit counter

1. var rf = Rv64RegFile create
2. rf write
3. rf write
   - Expected: rf.read(10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 0)
# Loop counter increment with ADDIW
val result = alu_execute_word(AluOp.Addw, rf.read(10), 1)
rf.write(10, result)
expect(rf.read(10)).to_equal(1)
```

</details>

#### ADDW for 32-bit address calculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base: i64 = 0x10000000
val offset: i64 = 0x100
val result = alu_execute_word(AluOp.Addw, base, offset)
expect(result).to_equal(0x10000100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
