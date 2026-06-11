# rv64_decoder_spec

> RV64I Instruction Decoder Unit Specification

<!-- sdn-diagram:id=rv64_decoder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_decoder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_decoder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_decoder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_decoder_spec

RV64I Instruction Decoder Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-DEC |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_decoder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64I Instruction Decoder Unit Specification

Tests field extraction, immediate decoding, and instruction classification
for the full RV64I base integer ISA.

## Scenarios

### RV64 instruction field extractors

#### extracts opcode from ADDI instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_addi(1, 0, 42)
expect(rv64_opcode(inst)).to_equal(OP_OP_IMM)
```

</details>

#### extracts rd from ADDI x5, x0, 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_addi(5, 0, 10)
expect(rv64_rd(inst)).to_equal(5)
```

</details>

#### extracts rs1 from ADD x1, x2, x3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_add(1, 2, 3)
expect(rv64_rs1(inst)).to_equal(2)
```

</details>

#### extracts rs2 from ADD x1, x2, x3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_add(1, 2, 3)
expect(rv64_rs2(inst)).to_equal(3)
```

</details>

#### extracts funct3 from LW (funct3=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_lw(1, 2, 0)
expect(rv64_funct3(inst)).to_equal(2)
```

</details>

#### extracts funct7 from SUB (funct7=0x20)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_sub(1, 2, 3)
expect(rv64_funct7(inst)).to_equal(0x20)
```

</details>

### RV64 immediate decoding

#### decodes positive I-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_addi(1, 0, 42)
expect(rv64_imm_i(inst)).to_equal(42)
```

</details>

#### decodes negative I-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = encode_addi(1, 0, -5)
expect(rv64_imm_i(inst)).to_equal(-5)
```

</details>

#### sign-extends small positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_extend(5, 12)).to_equal(5)
```

</details>

#### sign-extends 12-bit negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_extend(0xFFF, 12)).to_equal(-1)
```

</details>

### Rv64Decoder

#### decodes ADDI as I-type with Add ALU op

1. var dec = create rv64 decoder
   - Expected: latch.valid is true
   - Expected: latch.rd equals `1`
   - Expected: latch.imm equals `42`
   - Expected: latch.alu_src_b_imm is true
   - Expected: latch.reg_write is true
   - Expected: latch.alu_op.to_text() equals `add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_addi(1, 0, 42)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.valid).to_equal(true)
expect(latch.rd).to_equal(1)
expect(latch.imm).to_equal(42)
expect(latch.alu_src_b_imm).to_equal(true)
expect(latch.reg_write).to_equal(true)
expect(latch.alu_op.to_text()).to_equal("add")
```

</details>

#### decodes ADD as R-type with Add ALU op

1. var dec = create rv64 decoder
   - Expected: latch.rd equals `3`
   - Expected: latch.rs1_val equals `100`
   - Expected: latch.rs2_val equals `200`
   - Expected: latch.alu_src_b_imm is false
   - Expected: latch.reg_write is true
   - Expected: latch.alu_op.to_text() equals `add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_add(3, 1, 2)
val latch = dec.decode(inst, 0, 100, 200)
expect(latch.rd).to_equal(3)
expect(latch.rs1_val).to_equal(100)
expect(latch.rs2_val).to_equal(200)
expect(latch.alu_src_b_imm).to_equal(false)
expect(latch.reg_write).to_equal(true)
expect(latch.alu_op.to_text()).to_equal("add")
```

</details>

#### decodes SUB as R-type with Sub ALU op

1. var dec = create rv64 decoder
   - Expected: latch.alu_op.to_text() equals `sub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_sub(3, 1, 2)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.alu_op.to_text()).to_equal("sub")
```

</details>

#### decodes LUI as U-type with PassB

1. var dec = create rv64 decoder
   - Expected: latch.rd equals `5`
   - Expected: latch.alu_op.to_text() equals `passb`
   - Expected: latch.reg_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_lui(5, 0x12345000)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.rd).to_equal(5)
expect(latch.alu_op.to_text()).to_equal("passb")
expect(latch.reg_write).to_equal(true)
```

</details>

#### decodes LW as load with mem_read and mem_to_reg

1. var dec = create rv64 decoder
   - Expected: latch.mem_read is true
   - Expected: latch.mem_to_reg is true
   - Expected: latch.reg_write is true
   - Expected: latch.rd equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_lw(4, 2, 8)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.mem_read).to_equal(true)
expect(latch.mem_to_reg).to_equal(true)
expect(latch.reg_write).to_equal(true)
expect(latch.rd).to_equal(4)
```

</details>

#### decodes SW as store with mem_write

1. var dec = create rv64 decoder
   - Expected: latch.mem_write is true
   - Expected: latch.reg_write is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_sw(3, 2, 16)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.mem_write).to_equal(true)
expect(latch.reg_write).to_equal(false)
```

</details>

#### decodes BEQ as branch

1. var dec = create rv64 decoder
   - Expected: latch.branch is true
   - Expected: latch.reg_write is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_beq(1, 2, 8)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.branch).to_equal(true)
expect(latch.reg_write).to_equal(false)
```

</details>

#### decodes JAL as jump with reg_write

1. var dec = create rv64 decoder
   - Expected: latch.jump is true
   - Expected: latch.reg_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_jal(1, 100)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.jump).to_equal(true)
expect(latch.reg_write).to_equal(true)
```

</details>

#### decodes ADDW (RV64I W-suffix) as addw ALU op

1. var dec = create rv64 decoder
   - Expected: latch.alu_op.to_text() equals `addw`
   - Expected: latch.reg_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_addw(3, 1, 2)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.alu_op.to_text()).to_equal("addw")
expect(latch.reg_write).to_equal(true)
```

</details>

#### decodes ADDIW (RV64I W-suffix immediate)

1. var dec = create rv64 decoder
   - Expected: latch.alu_op.to_text() equals `addw`
   - Expected: latch.alu_src_b_imm is true
   - Expected: latch.imm equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_addiw(5, 1, 10)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.alu_op.to_text()).to_equal("addw")
expect(latch.alu_src_b_imm).to_equal(true)
expect(latch.imm).to_equal(10)
```

</details>

#### decodes LD (64-bit load, RV64I)

1. var dec = create rv64 decoder
   - Expected: latch.mem_read is true
   - Expected: latch.funct3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_ld(4, 2, 0)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.mem_read).to_equal(true)
expect(latch.funct3).to_equal(3)
```

</details>

#### decodes SD (64-bit store, RV64I)

1. var dec = create rv64 decoder
   - Expected: latch.mem_write is true
   - Expected: latch.funct3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = create_rv64_decoder()
val inst = encode_sd(4, 2, 0)
val latch = dec.decode(inst, 0, 0, 0)
expect(latch.mem_write).to_equal(true)
expect(latch.funct3).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
