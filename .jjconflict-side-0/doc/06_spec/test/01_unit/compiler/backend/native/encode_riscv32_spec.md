# Encode Riscv32 Specification

> <details>

<!-- sdn-diagram:id=encode_riscv32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_riscv32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_riscv32_spec -> std
encode_riscv32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_riscv32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Riscv32 Specification

## Scenarios

### Encode Riscv32

#### retains ELF32 constants for the RV32 Linux lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ELF32_EI_CLASS).to_equal(1)
expect(ELF32_HEADER_SIZE).to_equal(52)
```

</details>

#### shares the Linux call relocation and ABI contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.call_plt_reloc).to_equal(19)
expect(contract.abi_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
```

</details>

#### encodes RV32 U-type LUI and AUIPC words

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_emit_u32_le([], -1)).to_equal([0xFF, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], -2)).to_equal([0xFE, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], -4294967297)).to_equal([0xFF, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], -4294967296)).to_equal([0x00, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], 4294967295)).to_equal([0xFF, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], 4294967296)).to_equal([0x00, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], 4294967297)).to_equal([0x01, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([0xAA], 0x12345678)).to_equal([0xAA, 0x78, 0x56, 0x34, 0x12])
expect(riscv_emit_u32_le([0xAA, 0xBB], 4294967295)).to_equal([0xAA, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([0xAA, 0xBB], -4294967297)).to_equal([0xAA, 0xBB, 0xFF, 0xFF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_u_type(0, 1, 0x37))).to_equal([0xB7, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_u_type(0x12345, 1, 0x37))).to_equal([0xB7, 0x50, 0x34, 0x12])
expect(riscv_emit_u32_le([], riscv_encode_u_type(0x12345, 1, 0x17))).to_equal([0x97, 0x50, 0x34, 0x12])
expect(riscv_emit_u32_le([], riscv_encode_u_type(-1, 1, 0x37))).to_equal([0xB7, 0xF0, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_u_type(-1, -1, -1))).to_equal([0x7F, 0xEF, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_u_type(-1048576, 1, 0x37))).to_equal([0xB7, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_u_type(1048575, 1, 0x37))).to_equal([0xB7, 0xF0, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_u_type(1048576, 1, 0x37))).to_equal([0xB7, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_u_type(1048577, 33, 183))).to_equal([0xB7, 0x10, 0x00, 0x00])
```

</details>

#### encodes RV32 R-type ADD and SUB words

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_emit_u32_le([], riscv_encode_r_type(0, 3, 2, 0, 1, 0x33))).to_equal([0xB3, 0x00, 0x31, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_r_type(0x20, 3, 2, 0, 1, 0x33))).to_equal([0xB3, 0x00, 0x31, 0x40])
expect(riscv_emit_u32_le([], riscv_encode_r_type(-1, -1, -1, -1, -1, -1))).to_equal([0x7F, 0x6F, 0xEF, 0xFD])
expect(riscv_emit_u32_le([], riscv_encode_r_type(129, 34, 33, 10, 33, 179))).to_equal([0xB3, 0xA0, 0x20, 0x02])
```

</details>

#### encodes RV32 ALU MachInst funct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_alu_funct3(RV_OP_DIV)).to_equal(4)
expect(riscv_alu_funct3(RV_OP_REM)).to_equal(6)
expect(riscv_alu_funct3(RV_OP_AND)).to_equal(7)
expect(riscv_alu_funct3(RV_OP_OR)).to_equal(6)
expect(riscv_alu_funct3(RV_OP_XOR)).to_equal(4)
expect(riscv_alu_funct3(RV_OP_SLL)).to_equal(1)
expect(riscv_alu_funct3(RV_OP_SRA)).to_equal(5)
expect(riscv_alu_funct3(RV_OP_SRL)).to_equal(5)
expect(riscv_alu_funct3(RV_OP_SLT)).to_equal(2)
expect(riscv_alu_funct3(RV_OP_SLTU)).to_equal(3)
expect(riscv_alu_funct7(RV_OP_SUB)).to_equal(0x20)
expect(riscv_alu_funct7(RV_OP_SRA)).to_equal(0x20)
expect(riscv_alu_funct7(RV_OP_MUL)).to_equal(0x01)
expect(riscv_alu_funct7(RV_OP_DIV)).to_equal(0x01)
expect(riscv_alu_funct7(RV_OP_REM)).to_equal(0x01)
expect(riscv_alu_funct3(999)).to_equal(0)
expect(riscv_alu_funct7(999)).to_equal(0)
val encoded = encode_module_rv32(rv32_alu_module())
expect(encoded[0].code).to_equal([0xB3, 0x00, 0x31, 0x00, 0xB3, 0x00, 0x31, 0x40, 0xB3, 0x00, 0x31, 0x02, 0xB3, 0x50, 0x31, 0x40])
```

</details>

#### encodes RV32 logical compare shift and divide MachInst words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_more_alu_module())
expect(encoded[0].code).to_equal([0xB3, 0x70, 0x31, 0x00, 0xB3, 0x60, 0x31, 0x00, 0xB3, 0x40, 0x31, 0x00, 0xB3, 0x10, 0x31, 0x00, 0xB3, 0x50, 0x31, 0x00, 0xB3, 0x20, 0x31, 0x00, 0xB3, 0x30, 0x31, 0x00, 0xB3, 0x40, 0x31, 0x02, 0xB3, 0x60, 0x31, 0x02])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 pseudo ALU MachInst words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_pseudo_alu_module())
expect(encoded[0].code).to_equal([0xB3, 0x00, 0x20, 0x40, 0x93, 0x40, 0xF1, 0xFF, 0x93, 0x30, 0x11, 0x00, 0xB3, 0x30, 0x20, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 MV LI and RET MachInst words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_pseudo_control_module())
expect(encoded[0].code).to_equal([0x93, 0x00, 0x01, 0x00, 0x93, 0x00, 0xA0, 0x02, 0x67, 0x80, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps unsupported RV32 LI constants inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(encode_li_rv32([], RV_X1, 4294967296)).to_equal([0x13, 0x00, 0x00, 0x00])
expect(encode_li_rv32([0xAA], RV_X1, 4294967296)).to_equal([0xAA, 0x13, 0x00, 0x00, 0x00])
expect(encode_li_rv32([], RV_X1, -2147483649)).to_equal([0x13, 0x00, 0x00, 0x00])
```

</details>

#### encodes RV32 immediate upper MachInst words

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_imm_upper_module())
expect(encoded[0].code).to_equal([0x93, 0x00, 0xC1, 0xFF, 0xB7, 0x50, 0x34, 0x12, 0x97, 0x50, 0x34, 0x12, 0x97, 0x00, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(1)
expect(encoded[0].relocations[0].offset).to_equal(12)
expect(encoded[0].relocations[0].symbol_name).to_equal("upper_target")
expect(encoded[0].relocations[0].reloc_type).to_equal(RV32_R_RISCV_CALL_PLT)
```

</details>

#### encodes RV32 negative load and store offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_memory_offset_module())
expect(encoded[0].code).to_equal([0x83, 0x20, 0xC1, 0xFF, 0x23, 0x2C, 0x31, 0xFE])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 LD and SD fallbacks as LW and SW

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_ld_sd_fallback_module())
expect(encoded[0].code).to_equal([0x83, 0x20, 0x41, 0xFF, 0x23, 0x28, 0x31, 0xFE])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 symbol calls with CALL_PLT relocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_symbol_call_module())
expect(encoded[0].code).to_equal([0x97, 0x00, 0x00, 0x00, 0xE7, 0x80, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(1)
expect(encoded[0].relocations[0].offset).to_equal(0)
expect(encoded[0].relocations[0].symbol_name).to_equal("callee")
expect(encoded[0].relocations[0].reloc_type).to_equal(RV32_R_RISCV_CALL_PLT)
expect(encoded[0].relocations[0].addend).to_equal(0)
```

</details>

#### encodes RV32 label calls as patched JAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_label_call_module())
expect(encoded[0].code).to_equal([0xEF, 0x00, 0x40, 0x00, 0x13, 0x00, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 malformed call operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_malformed_call_module())
expect(encoded[0].code).to_equal(riscv_expected_nops(6))
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 JALR signed immediates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_jalr_module())
expect(encoded[0].code).to_equal([0xE7, 0x00, 0xC1, 0xFF])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 malformed data operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_malformed_operand_module())
expect(encoded[0].code).to_equal(riscv_expected_nops(47))
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### expands RV32 LI as ADDI or LUI plus ADDI

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(encode_li_rv32([], 1, 42)).to_equal([0x93, 0x00, 0xA0, 0x02])
expect(encode_li_rv32([0xAA], 1, 42)).to_equal([0xAA, 0x93, 0x00, 0xA0, 0x02])
expect(encode_li_rv32([], 1, -1)).to_equal([0x93, 0x00, 0xF0, 0xFF])
expect(encode_li_rv32([], 1, 2047)).to_equal([0x93, 0x00, 0xF0, 0x7F])
expect(encode_li_rv32([], 1, -2048)).to_equal([0x93, 0x00, 0x00, 0x80])
expect(encode_li_rv32([], 1, 2048)).to_equal([0xB7, 0x10, 0x00, 0x00, 0x93, 0x80, 0x00, 0x80])
expect(encode_li_rv32([0xAA], 1, 2048)).to_equal([0xAA, 0xB7, 0x10, 0x00, 0x00, 0x93, 0x80, 0x00, 0x80])
expect(encode_li_rv32([], 1, -2049)).to_equal([0xB7, 0xF0, 0xFF, 0xFF, 0x93, 0x80, 0xF0, 0x7F])
expect(encode_li_rv32([0xAA], 1, -2049)).to_equal([0xAA, 0xB7, 0xF0, 0xFF, 0xFF, 0x93, 0x80, 0xF0, 0x7F])
expect(encode_li_rv32([], 1, 4097)).to_equal([0xB7, 0x10, 0x00, 0x00, 0x93, 0x80, 0x10, 0x00])
expect(encode_li_rv32([], 1, -2147483648)).to_equal([0xB7, 0x00, 0x00, 0x80])
expect(encode_li_rv32([], 1, 2147483648)).to_equal([0xB7, 0x00, 0x00, 0x80])
expect(encode_li_rv32([0xAA], 1, 2147483648)).to_equal([0xAA, 0xB7, 0x00, 0x00, 0x80])
expect(encode_li_rv32([], 1, 4294967295)).to_equal([0x93, 0x00, 0xF0, 0xFF])
expect(encode_li_rv32([0xAA], 1, 4294967295)).to_equal([0xAA, 0x93, 0x00, 0xF0, 0xFF])
```

</details>

#### encodes RV32 store branch and jump immediates

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_emit_u32_le([], riscv_encode_s_type(20, 2, 1, 2, 0x23))).to_equal([0x23, 0xAA, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_s_type(-1, -1, -1, -1, -1))).to_equal([0x7F, 0x7F, 0xEF, 0xFD])
expect(riscv_emit_u32_le([], riscv_encode_i_type(-1, 2, 0, 1, 0x13))).to_equal([0x93, 0x00, 0xF1, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_i_type(-1, -1, -1, -1, -1))).to_equal([0x7F, 0x6F, 0xEF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_i_type(-2048, 2, 0, 1, 0x13))).to_equal([0x93, 0x00, 0x01, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_i_type(-2049, 2, 0, 1, 0x13))).to_equal([0x93, 0x00, 0xF1, 0x7F])
expect(riscv_emit_u32_le([], riscv_encode_i_type(2047, 2, 0, 1, 0x13))).to_equal([0x93, 0x00, 0xF1, 0x7F])
expect(riscv_emit_u32_le([], riscv_encode_i_type(2048, 2, 0, 1, 0x13))).to_equal([0x93, 0x00, 0x01, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_i_type(4097, 33, 10, 33, 147))).to_equal([0x93, 0xA0, 0x10, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_s_type(-4, 2, 1, 2, 0x23))).to_equal([0x23, 0xAE, 0x20, 0xFE])
expect(riscv_emit_u32_le([], riscv_encode_s_type(-2048, 2, 1, 2, 0x23))).to_equal([0x23, 0xA0, 0x20, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_s_type(2047, 2, 1, 2, 0x23))).to_equal([0xA3, 0xAF, 0x20, 0x7E])
expect(riscv_emit_u32_le([], riscv_encode_s_type(2048, 2, 1, 2, 0x23))).to_equal([0x23, 0xA0, 0x20, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_s_type(4096, 2, 1, 2, 0x23))).to_equal([0x23, 0xA0, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_s_type(-4097, 2, 1, 2, 0x23))).to_equal([0xA3, 0xAF, 0x20, 0xFE])
expect(riscv_emit_u32_le([], riscv_encode_s_type(4097, 34, 33, 10, 163))).to_equal([0xA3, 0xA0, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(0, 2, 1, 0, 0x63))).to_equal([0x63, 0x80, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(2, 2, 1, 0, 0x63))).to_equal([0x63, 0x81, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(3, 2, 1, 0, 0x63))).to_equal([0x63, 0x81, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-2, 2, 1, 0, 0x63))).to_equal([0xE3, 0x8F, 0x20, 0xFE])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-3, 2, 1, 0, 0x63))).to_equal([0xE3, 0x8E, 0x20, 0xFE])
expect(riscv_emit_u32_le([], riscv_encode_b_type(16, 2, 1, 0, 0x63))).to_equal([0x63, 0x88, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-4, 2, 1, 0, 0x63))).to_equal([0xE3, 0x8E, 0x20, 0xFE])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-4096, 2, 1, 0, 0x63))).to_equal([0x63, 0x80, 0x20, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_b_type(4094, 2, 1, 0, 0x63))).to_equal([0xE3, 0x8F, 0x20, 0x7E])
expect(riscv_emit_u32_le([], riscv_encode_b_type(4096, 2, 1, 0, 0x63))).to_equal([0x63, 0x80, 0x20, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-4098, 2, 1, 0, 0x63))).to_equal([0xE3, 0x8F, 0x20, 0x7E])
expect(riscv_emit_u32_le([], riscv_encode_b_type(8194, 34, 33, 10, 227))).to_equal([0x63, 0xA1, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_b_type(-1, -1, -1, -1, -1))).to_equal([0x7F, 0x7F, 0xEF, 0xFD])
expect(riscv_emit_u32_le([], riscv_encode_j_type(0, 1, 0x6F))).to_equal([0xEF, 0x00, 0x00, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_j_type(2, 1, 0x6F))).to_equal([0xEF, 0x00, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_j_type(3, 1, 0x6F))).to_equal([0xEF, 0x00, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-2, 1, 0x6F))).to_equal([0xEF, 0xF0, 0xFF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-3, 1, 0x6F))).to_equal([0xEF, 0xF0, 0xDF, 0xFF])
expect(riscv_emit_u32_le([], riscv_encode_j_type(2048, 1, 0x6F))).to_equal([0xEF, 0x00, 0x10, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-2048, 1, 0x6F))).to_equal([0xEF, 0xF0, 0x1F, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-1048576, 1, 0x6F))).to_equal([0xEF, 0x00, 0x00, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_j_type(1048574, 1, 0x6F))).to_equal([0xEF, 0xF0, 0xFF, 0x7F])
expect(riscv_emit_u32_le([], riscv_encode_j_type(1048576, 1, 0x6F))).to_equal([0xEF, 0x00, 0x00, 0x80])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-1048578, 1, 0x6F))).to_equal([0xEF, 0xF0, 0xFF, 0x7F])
expect(riscv_emit_u32_le([], riscv_encode_j_type(2097154, 33, 239))).to_equal([0xEF, 0x00, 0x20, 0x00])
expect(riscv_emit_u32_le([], riscv_encode_j_type(-1, -1, -1))).to_equal([0x7F, 0xEF, 0xFF, 0xFF])
```

</details>

#### checks RV32 branch and jump patch range edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_offset_fits_branch(-4096)).to_equal(true)
expect(riscv_offset_fits_branch(0)).to_equal(true)
expect(riscv_offset_fits_branch(2)).to_equal(true)
expect(riscv_offset_fits_branch(-2)).to_equal(true)
expect(riscv_offset_fits_branch(4094)).to_equal(true)
expect(riscv_offset_fits_branch(-4098)).to_equal(false)
expect(riscv_offset_fits_branch(4096)).to_equal(false)
expect(riscv_offset_fits_branch(-4095)).to_equal(false)
expect(riscv_offset_fits_branch(4093)).to_equal(false)
expect(riscv_offset_fits_branch(-1)).to_equal(false)
expect(riscv_offset_fits_branch(1)).to_equal(false)
expect(riscv_offset_fits_jal(-1048576)).to_equal(true)
expect(riscv_offset_fits_jal(0)).to_equal(true)
expect(riscv_offset_fits_jal(2)).to_equal(true)
expect(riscv_offset_fits_jal(-2)).to_equal(true)
expect(riscv_offset_fits_jal(1048574)).to_equal(true)
expect(riscv_offset_fits_jal(-1048578)).to_equal(false)
expect(riscv_offset_fits_jal(1048576)).to_equal(false)
expect(riscv_offset_fits_jal(-1048575)).to_equal(false)
expect(riscv_offset_fits_jal(1048573)).to_equal(false)
expect(riscv_offset_fits_jal(-1)).to_equal(false)
expect(riscv_offset_fits_jal(1)).to_equal(false)
```

</details>

#### checks RV32 operand predicate edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_operand_is_reg(op_phys(0))).to_equal(true)
expect(riscv_operand_is_reg(op_phys(31))).to_equal(true)
expect(riscv_operand_is_reg(op_phys(-1))).to_equal(false)
expect(riscv_operand_is_reg(op_phys(32))).to_equal(false)
expect(riscv_operand_is_reg(op_phys(99))).to_equal(false)
expect(riscv_operand_is_reg(op_imm(0))).to_equal(false)
expect(riscv_operand_is_reg(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_signed_12_imm(op_imm(-2048))).to_equal(true)
expect(riscv_operand_is_signed_12_imm(op_imm(0))).to_equal(true)
expect(riscv_operand_is_signed_12_imm(op_imm(2047))).to_equal(true)
expect(riscv_operand_is_signed_12_imm(op_imm(-2049))).to_equal(false)
expect(riscv_operand_is_signed_12_imm(op_imm(2048))).to_equal(false)
expect(riscv_operand_is_signed_12_imm(op_label(1))).to_equal(false)
expect(riscv_operand_is_signed_12_imm(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_signed_12_imm(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_u20_imm(op_imm(0))).to_equal(true)
expect(riscv_operand_is_u20_imm(op_imm(1048575))).to_equal(true)
expect(riscv_operand_is_u20_imm(op_imm(-1))).to_equal(false)
expect(riscv_operand_is_u20_imm(op_imm(1048576))).to_equal(false)
expect(riscv_operand_is_u20_imm(op_label(1))).to_equal(false)
expect(riscv_operand_is_u20_imm(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_u20_imm(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_mem(op_mem(physical_reg(31), 0))).to_equal(true)
expect(riscv_operand_is_mem(op_mem(physical_reg(-1), 0))).to_equal(false)
expect(riscv_operand_is_mem(op_mem(physical_reg(32), 0))).to_equal(false)
expect(riscv_operand_is_mem(op_mem(physical_reg(99), 0))).to_equal(false)
expect(riscv_operand_is_mem(op_imm(0))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(RV_X2), -2048))).to_equal(true)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(RV_X2), 0))).to_equal(true)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(RV_X2), 2047))).to_equal(true)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(RV_X2), -2049))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(RV_X2), 2048))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(-1), 0))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(32), 0))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_mem(physical_reg(99), 0))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_imm(0))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_sym("target"))).to_equal(false)
expect(riscv_operand_mem_offset_is_signed_12(op_label(1))).to_equal(false)
expect(riscv_operand_is_imm(op_imm(0))).to_equal(true)
expect(riscv_operand_is_imm(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_imm(op_label(1))).to_equal(false)
expect(riscv_operand_is_imm(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_imm_or_sym(op_imm(0))).to_equal(true)
expect(riscv_operand_is_imm_or_sym(op_sym("target"))).to_equal(true)
expect(riscv_operand_is_imm_or_sym(op_label(1))).to_equal(false)
expect(riscv_operand_is_imm_or_sym(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_label(op_label(1))).to_equal(true)
expect(riscv_operand_is_label(op_imm(1))).to_equal(false)
expect(riscv_operand_is_label(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_label(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_imm_or_label(op_imm(1))).to_equal(true)
expect(riscv_operand_is_imm_or_label(op_label(1))).to_equal(true)
expect(riscv_operand_is_imm_or_label(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_imm_or_label(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_imm(-1048576))).to_equal(true)
expect(riscv_operand_is_jal_imm(op_imm(-2))).to_equal(true)
expect(riscv_operand_is_jal_imm(op_imm(0))).to_equal(true)
expect(riscv_operand_is_jal_imm(op_imm(2))).to_equal(true)
expect(riscv_operand_is_jal_imm(op_imm(1048574))).to_equal(true)
expect(riscv_operand_is_jal_imm(op_imm(-1048578))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_imm(1))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_imm(1048576))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_sym("target"))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_label(1))).to_equal(false)
expect(riscv_operand_is_jal_imm(op_mem(physical_reg(RV_X2), 0))).to_equal(false)
```

</details>

#### patches RV32 backward branch and jump labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_backward_patch_module())
expect(encoded[0].code).to_equal([0x13, 0x00, 0x00, 0x00, 0xE3, 0x8E, 0x20, 0xFE, 0xEF, 0xF0, 0x9F, 0xFF])
```

</details>

#### patches RV32 forward branch and jump labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_forward_patch_module())
expect(encoded[0].code).to_equal([0x63, 0x84, 0x20, 0x00, 0xEF, 0x00, 0x40, 0x00, 0x13, 0x00, 0x00, 0x00])
```

</details>

#### keeps RV32 out-of-range resolved branches inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_far_branch_module())
expect(encoded[0].code.len()).to_equal(4104)
expect(encoded[0].code[0]).to_equal(0x13)
expect(encoded[0].code[1]).to_equal(0x00)
expect(encoded[0].code[2]).to_equal(0x00)
expect(encoded[0].code[3]).to_equal(0x00)
```

</details>

#### keeps RV32 malformed branch and jump targets inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_malformed_jump_module())
expect(encoded[0].code).to_equal(riscv_expected_nops(27))
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 unresolved label jumps inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_unresolved_label_module())
expect(encoded[0].code).to_equal([0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 short control operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_short_control_operand_module())
expect(encoded[0].code).to_equal([0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 short common operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_short_common_operand_module())
expect(encoded[0].code).to_equal(riscv_expected_nops(7))
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 malformed common operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_malformed_common_operand_module())
expect(encoded[0].code).to_equal(riscv_expected_nops(52))
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### keeps RV32 short data operands inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_short_data_operand_module())
expect(encoded[0].code).to_equal([0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 immediate JAL offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_immediate_jump_module())
expect(encoded[0].code).to_equal([0xEF, 0x00, 0x20, 0x00, 0xEF, 0xF0, 0xFF, 0xFF])
expect(encoded[0].relocations.len()).to_equal(0)
```

</details>

#### encodes RV32 unknown opcodes as EBREAK

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = encode_module_rv32(rv32_unknown_opcode_module())
expect(encoded[0].code).to_equal([0x73, 0x00, 0x10, 0x00])
```

</details>

#### encodes RV32 branch funct3 labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_branch_funct3(RV_OP_BEQ)).to_equal(0)
expect(riscv_branch_funct3(RV_OP_BNE)).to_equal(1)
expect(riscv_branch_funct3(RV_OP_BLT)).to_equal(4)
expect(riscv_branch_funct3(RV_OP_BGE)).to_equal(5)
expect(riscv_branch_funct3(999)).to_equal(0)
val encoded = encode_module_rv32(rv32_branch_funct_module())
expect(encoded[0].code).to_equal([0x63, 0x96, 0x20, 0x00, 0x63, 0xC4, 0x20, 0x00, 0x63, 0xD2, 0x20, 0x00, 0x13, 0x00, 0x00, 0x00])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/encode_riscv32_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Encode Riscv32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
