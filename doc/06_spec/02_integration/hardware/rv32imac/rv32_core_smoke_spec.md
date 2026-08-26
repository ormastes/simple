# RV32IMAC Core Smoke Tests

> Smoke tests for the RV32IMAC core. Verifies basic instruction execution through GHDL simulation: NOP, ADD, branch, load/store.

<!-- sdn-diagram:id=rv32_core_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_core_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_core_smoke_spec -> std
rv32_core_smoke_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_core_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32IMAC Core Smoke Tests

Smoke tests for the RV32IMAC core. Verifies basic instruction execution through GHDL simulation: NOP, ADD, branch, load/store.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-CORE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Smoke tests for the RV32IMAC core. Verifies basic instruction execution
through GHDL simulation: NOP, ADD, branch, load/store.

## Scenarios

### RV32 Register File

#### x0 always reads as zero

1. var rf = Rv32RegFile create
2. rf write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(0, 0xDEADBEEF)
expect(rf.read(0)).to_equal(0)
```

</details>

#### writes and reads back correctly

1. var rf = Rv32RegFile create
2. rf write
   - Expected: rf.read(1) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(1, 0x12345678)
expect(rf.read(1)).to_equal(0x12345678)
```

</details>

#### handles all 32 registers

1. var rf = Rv32RegFile create
2. rf write
   - Expected: rf.read(0) equals `0`
   - Expected: rf.read(1) equals `100`
   - Expected: rf.read(31) equals `3100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
var i = 1
while i < 32:
    rf.write(i, i * 100)
    i = i + 1
expect(rf.read(0)).to_equal(0)
expect(rf.read(1)).to_equal(100)
expect(rf.read(31)).to_equal(3100)
```

</details>

### RV32 ALU

#### computes ADD correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Add, 5, 3)).to_equal(8)
```

</details>

#### computes SUB correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sub, 10, 3)).to_equal(7)
```

</details>

#### computes AND correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 0xFF00FF00, 0x0F0F0F0F)).to_equal(0x0F000F00)
```

</details>

#### computes OR correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0xFF000000, 0x00FF0000)).to_equal(0xFFFF0000)
```

</details>

#### computes XOR correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xFF00FF00, 0xFFFF0000)).to_equal(0x00FFFF00)
```

</details>

#### computes SLL correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sll, 1, 4)).to_equal(16)
```

</details>

#### computes SRL correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Srl, 256, 4)).to_equal(16)
```

</details>

#### computes SLT correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 1)).to_equal(1)
```

</details>

#### computes SLTU correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 1)).to_equal(0)
```

</details>

### RV32 Branch Resolution

#### BEQ taken when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_branch(BranchOp.Beq, 42, 42)).to_equal(true)
```

</details>

#### BEQ not taken when unequal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_branch(BranchOp.Beq, 42, 43)).to_equal(false)
```

</details>

#### BNE taken when unequal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_branch(BranchOp.Bne, 42, 43)).to_equal(true)
```

</details>

#### BLT taken for signed less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_branch(BranchOp.Blt, 0xFFFFFFFF, 0)).to_equal(true)
```

</details>

#### JAL always taken

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_branch_target("branch", 0x1000, 0, 0)).to_equal(0x1000)
```

</details>

#### computes branch target from PC+imm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_branch_target("branch", 0x1000, 0, 0x100)).to_equal(0x1100)
```

</details>

#### computes JALR target from rs1+imm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_branch_target("jalr", 0x1000, 0x2000, 0x10)).to_equal(0x2010)
```

</details>

### RV32 Immediate Decoding

#### decodes I-type positive immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 100 << 20  # imm=100 in bits [31:20]
expect(decode_imm_i(instr)).to_equal(100)
```

</details>

#### decodes U-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x12345000  # Upper 20 bits in place
expect(decode_imm_u(instr)).to_equal(0x12345000)
```

</details>

### RV32 Memory Access

#### loads a word from memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memory = [0x12345678, 0xDEADBEEF]
expect(mem_load(memory, 0, MemWidth.Word, false)).to_equal(0x12345678)
expect(mem_load(memory, 4, MemWidth.Word, false)).to_equal(0xDEADBEEF)
```

</details>

#### loads a byte with sign extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, true)).to_equal(0xFFFFFFFF)
```

</details>

#### loads a byte without sign extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, false)).to_equal(0xFF)
```

</details>

#### stores a word to memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memory = [0, 0]
val updated = mem_store(memory, 0, 0xCAFEBABE, MemWidth.Word)
expect(updated[0]).to_equal(0xCAFEBABE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
