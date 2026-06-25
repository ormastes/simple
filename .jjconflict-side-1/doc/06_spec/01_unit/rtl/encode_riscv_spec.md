# RTL RISC-V Encode Spec

> Unit tests for RTL encode functions in `src/compiler/70.backend/backend/native/encode_riscv32.spl`, `src/compiler/70.backend/backend/native/encode_riscv64.spl`, and `src/compiler/70.backend/backend/native/riscv_encoding.spl`.

<!-- sdn-diagram:id=encode_riscv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_riscv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_riscv_spec -> std
encode_riscv_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_riscv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RTL RISC-V Encode Spec

Unit tests for RTL encode functions in `src/compiler/70.backend/backend/native/encode_riscv32.spl`, `src/compiler/70.backend/backend/native/encode_riscv64.spl`, and `src/compiler/70.backend/backend/native/riscv_encoding.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/rtl/encode_riscv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RTL encode functions in
`src/compiler/70.backend/backend/native/encode_riscv32.spl`,
`src/compiler/70.backend/backend/native/encode_riscv64.spl`, and
`src/compiler/70.backend/backend/native/riscv_encoding.spl`.

Covers AC-3 / AC-4 by encoding known instructions and verifying the produced
byte words against reference values from the RISC-V ISA spec.

Reference encoding formula:
- R-type: funct7[31:25] | rs2[24:20] | rs1[19:15] | funct3[14:12] | rd[11:7] | opcode[6:0]
- I-type: imm[11:0][31:20] | rs1[19:15] | funct3[14:12] | rd[11:7] | opcode[6:0]
- U-type: imm[31:12][31:12] | rd[11:7] | opcode[6:0]

These specs WILL FAIL until Team F lands and wires up the import paths.

## Scenarios

### AC-3/AC-4 riscv_encode_i_type

#### AC-4: ADDI x0, x0, 0 encodes to NOP (0x00000013)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# imm12=0, rs1=0(x0), funct3=0, rd=0(x0), opcode=0x13
val word = riscv_encode_i_type(0, 0, 0, 0, 0x13)
expect(word).to_equal(0x00000013)
```

</details>

#### AC-4: ADDI x5, x0, 1 encodes to 0x00100293

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# imm12=1, rs1=0, funct3=0, rd=5, opcode=0x13
# (1<<20)|(0<<15)|(0<<12)|(5<<7)|0x13 = 0x00100293
val word = riscv_encode_i_type(1, 0, 0, 5, 0x13)
expect(word).to_equal(0x00100293)
```

</details>

#### AC-4: ADDI x1, x0, -1 encodes to 0xFFF00093

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# imm12=-1 (0xFFF), rs1=0, funct3=0, rd=1, opcode=0x13
# (0xFFF<<20)|(0<<15)|(0<<12)|(1<<7)|0x13 = 0xFFF00093
val word = riscv_encode_i_type(0xFFF, 0, 0, 1, 0x13)
expect(word).to_equal(0xFFF00093)
```

</details>

#### AC-4: LW x2, 4(x3) encodes to 0x00412103

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LW: imm=4, rs1=3, funct3=2, rd=2, opcode=0x03
# (4<<20)|(3<<15)|(2<<12)|(2<<7)|0x03 = 0x00412103
val word = riscv_encode_i_type(4, 3, 2, 2, 0x03)
expect(word).to_equal(0x00412103)
```

</details>

### AC-3/AC-4 riscv_encode_r_type

#### AC-4: ADD x1, x2, x3 encodes to 0x003100B3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct7=0, rs2=3, rs1=2, funct3=0, rd=1, opcode=0x33
# (0<<25)|(3<<20)|(2<<15)|(0<<12)|(1<<7)|0x33 = 0x003100B3
val word = riscv_encode_r_type(0, 3, 2, 0, 1, 0x33)
expect(word).to_equal(0x003100B3)
```

</details>

#### AC-4: SUB x1, x2, x3 encodes to 0x403100B3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct7=0x20, rs2=3, rs1=2, funct3=0, rd=1, opcode=0x33
# (0x20<<25)|(3<<20)|(2<<15)|(0<<12)|(1<<7)|0x33 = 0x403100B3
val word = riscv_encode_r_type(0x20, 3, 2, 0, 1, 0x33)
expect(word).to_equal(0x403100B3)
```

</details>

#### AC-4: AND x4, x5, x6 encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct7=0, rs2=6, rs1=5, funct3=7(AND), rd=4, opcode=0x33
# (0<<25)|(6<<20)|(5<<15)|(7<<12)|(4<<7)|0x33
# = 0x0062F233
val word = riscv_encode_r_type(0, 6, 5, 7, 4, 0x33)
expect(word).to_equal(0x0062F233)
```

</details>

### AC-3/AC-4 riscv_encode_u_type

#### AC-4: LUI x1, 1 encodes to 0x000010B7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# imm20=1, rd=1, opcode=0x37 (LUI)
# (1<<12)|(1<<7)|0x37 = 0x000010B7
val word = riscv_encode_u_type(1, 1, 0x37)
expect(word).to_equal(0x000010B7)
```

</details>

#### AC-4: LUI x0, 0 encodes to pure LUI opcode 0x00000037

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val word = riscv_encode_u_type(0, 0, 0x37)
expect(word).to_equal(0x00000037)
```

</details>

### AC-3/AC-4 riscv_emit_u32_le

#### AC-4: emitting NOP adds 4 bytes to an empty buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [i64] = []
val result = riscv_emit_u32_le(buf, 0x00000013)
expect(result.len()).to_equal(4)
```

</details>

#### AC-4: emitting 0x00000013 produces correct LE bytes [0x13, 0x00, 0x00, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [i64] = []
val result = riscv_emit_u32_le(buf, 0x00000013)
expect(result[0]).to_equal(0x13)
expect(result[1]).to_equal(0x00)
expect(result[2]).to_equal(0x00)
expect(result[3]).to_equal(0x00)
```

</details>

#### AC-4: emitting 0x00100293 produces bytes [0x93, 0x02, 0x10, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ADDI x5, x0, 1 = 0x00100293
var buf: [i64] = []
val result = riscv_emit_u32_le(buf, 0x00100293)
expect(result[0]).to_equal(0x93)
expect(result[1]).to_equal(0x02)
expect(result[2]).to_equal(0x10)
expect(result[3]).to_equal(0x00)
```

</details>

### AC-3/AC-4 encode_li_rv32

#### AC-4: encode_li_rv32 with imm=0 emits single 4-byte instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_rv32(empty, 5, 0)
# ADDI x5, x0, 0 = NOP variant = 4 bytes
expect(result.len()).to_equal(4)
```

</details>

#### AC-4: encode_li_rv32 with imm=1 produces ADDI x5, x0, 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_rv32(empty, 5, 1)
# 4 bytes for ADDI
expect(result.len()).to_equal(4)
# LE bytes of 0x00100293: 0x93, 0x02, 0x10, 0x00
expect(result[0]).to_equal(0x93)
expect(result[1]).to_equal(0x02)
expect(result[2]).to_equal(0x10)
expect(result[3]).to_equal(0x00)
```

</details>

#### AC-4: encode_li_rv32 with imm=2048 emits LUI+ADDI (8 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2048 does not fit in signed 12-bit [-2048,2047], needs LUI+ADDI
var empty: [i64] = []
val result = encode_li_rv32(empty, 1, 2048)
expect(result.len()).to_equal(8)
```

</details>

#### AC-4: encode_li_rv32 with imm=-1 emits ADDI (fits in 12-bit signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_rv32(empty, 1, -1)
expect(result.len()).to_equal(4)
```

</details>

#### AC-4: encode_li_rv32 output appends to existing buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var initial: [i64] = [0x00]
val result  = encode_li_rv32(initial, 1, 0)
# original 1 byte + 4 new bytes = 5
expect(result.len()).to_equal(5)
```

</details>

### AC-3/AC-4 encode_li_riscv64

#### AC-4: encode_li_riscv64 with imm=0 emits single ADDI (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_riscv64(empty, 5, 0)
expect(result.len()).to_equal(4)
```

</details>

#### AC-4: encode_li_riscv64 with imm=1 produces ADDI x5, x0, 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_riscv64(empty, 5, 1)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(0x93)
expect(result[1]).to_equal(0x02)
expect(result[2]).to_equal(0x10)
expect(result[3]).to_equal(0x00)
```

</details>

#### AC-4: encode_li_riscv64 with imm=2048 emits LUI+ADDI (8 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_riscv64(empty, 1, 2048)
expect(result.len()).to_equal(8)
```

</details>

#### AC-4: encode_li_riscv64 with imm=-1 emits single ADDI (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [i64] = []
val result = encode_li_riscv64(empty, 1, -1)
expect(result.len()).to_equal(4)
```

</details>

#### AC-4: encode_li_riscv64 appends to existing buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var initial: [i64] = [0x00]
val result  = encode_li_riscv64(initial, 1, 0)
expect(result.len()).to_equal(5)
```

</details>

### AC-3/AC-4 rv32_new_encode_context

#### AC-4: rv32_new_encode_context returns context with empty code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = rv32_new_encode_context()
expect(ctx.code.len()).to_equal(0)
expect(ctx.relocations.len()).to_equal(0)
```

</details>

### AC-3/AC-4 rv64_new_encode_context

#### AC-4: rv64_new_encode_context returns context with empty code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = rv64_new_encode_context()
expect(ctx.code.len()).to_equal(0)
expect(ctx.relocations.len()).to_equal(0)
```

</details>

### AC-3/AC-4 rv32_encode_contract

#### AC-4: rv32_encode_contract is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = rv32_encode_contract()
expect(contract.pointer_bits).to_equal(32)
expect(contract.abi_text()).to_contain("ilp32")
```

</details>

### AC-3/AC-4 rv64_encode_contract

#### AC-4: rv64_encode_contract is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = rv64_encode_contract()
expect(contract.pointer_bits).to_equal(64)
expect(contract.abi_text()).to_contain("lp64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
