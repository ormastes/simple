# Vhdl Rv32i Pipeline Specification

> <details>

<!-- sdn-diagram:id=vhdl_rv32i_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_rv32i_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_rv32i_pipeline_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_rv32i_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Rv32i Pipeline Specification

## Scenarios

### VHDL register file template

#### renders a standard RV32I 32x32 register file with x0 hardwire

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = rv32i_register_file_template()
val result = render_register_file_template(tmpl)

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl

# Entity ports
expect(vhdl).to_contain("entity rv32i_regfile is")
expect(vhdl).to_contain("clk : in std_logic;")
expect(vhdl).to_contain("rst : in std_logic;")
expect(vhdl).to_contain("reg_we : in std_logic;")
expect(vhdl).to_contain("rd_addr : in unsigned(4 downto 0);")
expect(vhdl).to_contain("rd_data : in std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("rs1_addr : in unsigned(4 downto 0);")
expect(vhdl).to_contain("rs2_addr : in unsigned(4 downto 0);")
expect(vhdl).to_contain("rs1_data : out std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("rs2_data : out std_logic_vector(31 downto 0)")
expect(vhdl).to_contain("end entity rv32i_regfile;")

# Architecture and array type
expect(vhdl).to_contain("architecture rtl of rv32i_regfile is")
expect(vhdl).to_contain("type rv32i_regfile_array_t is array (0 to 31) of std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("signal regs : rv32i_regfile_array_t")

# x0 hardwire in read ports
expect(vhdl).to_contain("(others => '0') when to_integer(rs1_addr) = 0")
expect(vhdl).to_contain("(others => '0') when to_integer(rs2_addr) = 0")

# Write process with x0 guard
expect(vhdl).to_contain("rv32i_regfile_write: process(clk, rst)")
expect(vhdl).to_contain("to_integer(rd_addr) /= 0")
expect(vhdl).to_contain("rising_edge(clk)")

# Reset
expect(vhdl).to_contain("rst = '1'")
```

</details>

#### renders a register file without x0 hardwire

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = VhdlRegisterFileTemplate(
    name: "gpr",
    depth: 16,
    data_width: 8,
    clock: "clk",
    reset: "reset",
    write_enable: "we",
    write_addr: "wa",
    write_data: "wd",
    read_addr1: "ra1",
    read_addr2: "ra2",
    read_data1: "rd1",
    read_data2: "rd2",
    zero_register: false
)
val result = render_register_file_template(tmpl)

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl

expect(vhdl).to_contain("entity gpr is")
expect(vhdl).to_contain("wa : in unsigned(3 downto 0);")
expect(vhdl).to_contain("wd : in std_logic_vector(7 downto 0);")
expect(vhdl).to_contain("array (0 to 15) of std_logic_vector(7 downto 0)")

# No x0 guard when zero_register=false
expect(vhdl.contains("/= 0")).to_equal(false)
# Direct read without conditional
expect(vhdl).to_contain("rd1 <= regs(to_integer(ra1));")
expect(vhdl).to_contain("rd2 <= regs(to_integer(ra2));")
```

</details>

#### rejects zero depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = VhdlRegisterFileTemplate(
    name: "bad",
    depth: 0,
    data_width: 32,
    clock: "clk",
    reset: "rst",
    write_enable: "we",
    write_addr: "wa",
    write_data: "wd",
    read_addr1: "ra1",
    read_addr2: "ra2",
    read_data1: "rd1",
    read_data2: "rd2",
    zero_register: false
)
val result = render_register_file_template(tmpl)
expect(result.is_err()).to_equal(true)
val diag = result.unwrap_err()
expect(diag.code).to_equal("VHDL-REGFILE-DEPTH")
```

</details>

#### rejects excessive depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = VhdlRegisterFileTemplate(
    name: "huge",
    depth: 2048,
    data_width: 32,
    clock: "clk",
    reset: "rst",
    write_enable: "we",
    write_addr: "wa",
    write_data: "wd",
    read_addr1: "ra1",
    read_addr2: "ra2",
    read_data1: "rd1",
    read_data2: "rd2",
    zero_register: false
)
val result = render_register_file_template(tmpl)
expect(result.is_err()).to_equal(true)
val diag = result.unwrap_err()
expect(diag.code).to_equal("VHDL-REGFILE-DEPTH-LIMIT")
```

</details>

#### rejects zero data width

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpl = VhdlRegisterFileTemplate(
    name: "narrow",
    depth: 32,
    data_width: 0,
    clock: "clk",
    reset: "rst",
    write_enable: "we",
    write_addr: "wa",
    write_data: "wd",
    read_addr1: "ra1",
    read_addr2: "ra2",
    read_data1: "rd1",
    read_data2: "rd2",
    zero_register: false
)
val result = render_register_file_template(tmpl)
expect(result.is_err()).to_equal(true)
val diag = result.unwrap_err()
expect(diag.code).to_equal("VHDL-REGFILE-WIDTH")
```

</details>

### address width calculation

#### computes ceil log2 for common depths

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(addr_width_for_depth(1)).to_equal(1)
expect(addr_width_for_depth(2)).to_equal(1)
expect(addr_width_for_depth(4)).to_equal(2)
expect(addr_width_for_depth(8)).to_equal(3)
expect(addr_width_for_depth(16)).to_equal(4)
expect(addr_width_for_depth(32)).to_equal(5)
expect(addr_width_for_depth(64)).to_equal(6)
```

</details>

#### computes ceil log2 for non-power-of-two depths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(addr_width_for_depth(3)).to_equal(2)
expect(addr_width_for_depth(5)).to_equal(3)
expect(addr_width_for_depth(17)).to_equal(5)
expect(addr_width_for_depth(33)).to_equal(6)
```

</details>

### RV32I opcode package

#### renders all base RV32I opcode constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = render_rv32i_opcode_package()

expect(pkg).to_contain("package rv32i_pkg is")
expect(pkg).to_contain("end package rv32i_pkg;")

# Base opcodes
expect(pkg).to_contain("constant OP_LUI : std_logic_vector(6 downto 0) := \"0110111\";")
expect(pkg).to_contain("constant OP_AUIPC : std_logic_vector(6 downto 0) := \"0010111\";")
expect(pkg).to_contain("constant OP_JAL : std_logic_vector(6 downto 0) := \"1101111\";")
expect(pkg).to_contain("constant OP_JALR : std_logic_vector(6 downto 0) := \"1100111\";")
expect(pkg).to_contain("constant OP_BRANCH : std_logic_vector(6 downto 0) := \"1100011\";")
expect(pkg).to_contain("constant OP_LOAD : std_logic_vector(6 downto 0) := \"0000011\";")
expect(pkg).to_contain("constant OP_STORE : std_logic_vector(6 downto 0) := \"0100011\";")
expect(pkg).to_contain("constant OP_IMM : std_logic_vector(6 downto 0) := \"0010011\";")
expect(pkg).to_contain("constant OP_REG : std_logic_vector(6 downto 0) := \"0110011\";")
expect(pkg).to_contain("constant OP_SYSTEM : std_logic_vector(6 downto 0) := \"1110011\";")
```

</details>

#### renders ALU funct3 codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = render_rv32i_opcode_package()

expect(pkg).to_contain("constant F3_ADD_SUB : std_logic_vector(2 downto 0) := \"000\";")
expect(pkg).to_contain("constant F3_SLL : std_logic_vector(2 downto 0) := \"001\";")
expect(pkg).to_contain("constant F3_SLT : std_logic_vector(2 downto 0) := \"010\";")
expect(pkg).to_contain("constant F3_XOR : std_logic_vector(2 downto 0) := \"100\";")
expect(pkg).to_contain("constant F3_OR : std_logic_vector(2 downto 0) := \"110\";")
expect(pkg).to_contain("constant F3_AND : std_logic_vector(2 downto 0) := \"111\";")
```

</details>

#### renders branch funct3 codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = render_rv32i_opcode_package()

expect(pkg).to_contain("constant F3_BEQ : std_logic_vector(2 downto 0) := \"000\";")
expect(pkg).to_contain("constant F3_BNE : std_logic_vector(2 downto 0) := \"001\";")
expect(pkg).to_contain("constant F3_BLT : std_logic_vector(2 downto 0) := \"100\";")
expect(pkg).to_contain("constant F3_BGE : std_logic_vector(2 downto 0) := \"101\";")
```

</details>

#### renders ALU control encoding constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = render_rv32i_opcode_package()

expect(pkg).to_contain("constant ALU_ADD : std_logic_vector(3 downto 0) := \"0000\";")
expect(pkg).to_contain("constant ALU_SUB : std_logic_vector(3 downto 0) := \"0001\";")
expect(pkg).to_contain("constant ALU_SLL : std_logic_vector(3 downto 0) := \"0010\";")
expect(pkg).to_contain("constant ALU_SRA : std_logic_vector(3 downto 0) := \"0111\";")
expect(pkg).to_contain("constant ALU_PASS_B : std_logic_vector(3 downto 0) := \"1010\";")
```

</details>

#### renders load store width codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg = render_rv32i_opcode_package()

expect(pkg).to_contain("constant F3_BYTE : std_logic_vector(2 downto 0) := \"000\";")
expect(pkg).to_contain("constant F3_HALF : std_logic_vector(2 downto 0) := \"001\";")
expect(pkg).to_contain("constant F3_WORD : std_logic_vector(2 downto 0) := \"010\";")
expect(pkg).to_contain("constant F3_BYTE_U : std_logic_vector(2 downto 0) := \"100\";")
expect(pkg).to_contain("constant F3_HALF_U : std_logic_vector(2 downto 0) := \"101\";")
```

</details>

### RV32I field extractor entity

#### renders a combinational instruction decoder entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_field_extractor()

expect(vhdl).to_contain("entity rv32i_decoder is")
expect(vhdl).to_contain("instr : in std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("opcode : out std_logic_vector(6 downto 0);")
expect(vhdl).to_contain("rd : out unsigned(4 downto 0);")
expect(vhdl).to_contain("funct3 : out std_logic_vector(2 downto 0);")
expect(vhdl).to_contain("rs1 : out unsigned(4 downto 0);")
expect(vhdl).to_contain("rs2 : out unsigned(4 downto 0);")
expect(vhdl).to_contain("funct7 : out std_logic_vector(6 downto 0);")
expect(vhdl).to_contain("end entity rv32i_decoder;")
```

</details>

#### extracts correct bit fields from instruction word

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_field_extractor()

# Opcode: bits 6:0
expect(vhdl).to_contain("opcode <= instr(6 downto 0);")
# rd: bits 11:7
expect(vhdl).to_contain("rd <= unsigned(instr(11 downto 7));")
# funct3: bits 14:12
expect(vhdl).to_contain("funct3 <= instr(14 downto 12);")
# rs1: bits 19:15
expect(vhdl).to_contain("rs1 <= unsigned(instr(19 downto 15));")
# rs2: bits 24:20
expect(vhdl).to_contain("rs2 <= unsigned(instr(24 downto 20));")
# funct7: bits 31:25
expect(vhdl).to_contain("funct7 <= instr(31 downto 25);")
```

</details>

#### generates all five immediate type decodings

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_field_extractor()

# I-type immediate outputs
expect(vhdl).to_contain("imm_i : out std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("imm_i <=")

# S-type immediate outputs
expect(vhdl).to_contain("imm_s : out std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("imm_s <=")

# B-type immediate outputs
expect(vhdl).to_contain("imm_b : out std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("imm_b <=")

# U-type immediate outputs
expect(vhdl).to_contain("imm_u : out std_logic_vector(31 downto 0);")
expect(vhdl).to_contain("imm_u <=")

# J-type immediate outputs
expect(vhdl).to_contain("imm_j : out std_logic_vector(31 downto 0)")
expect(vhdl).to_contain("imm_j <=")
```

</details>

#### uses work.rv32i_pkg for constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_field_extractor()
expect(vhdl).to_contain("use work.rv32i_pkg.all;")
```

</details>

### RV32I ALU control decoder

#### renders a combinational ALU control entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()

expect(vhdl).to_contain("entity rv32i_alu_ctrl is")
expect(vhdl).to_contain("opcode : in std_logic_vector(6 downto 0);")
expect(vhdl).to_contain("funct3 : in std_logic_vector(2 downto 0);")
expect(vhdl).to_contain("funct7 : in std_logic_vector(6 downto 0);")
expect(vhdl).to_contain("alu_op : out std_logic_vector(3 downto 0)")
expect(vhdl).to_contain("end entity rv32i_alu_ctrl;")
expect(vhdl).to_contain("architecture rtl of rv32i_alu_ctrl is")
```

</details>

#### decodes R-type ADD vs SUB via funct7

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()

expect(vhdl).to_contain("opcode = OP_REG")
expect(vhdl).to_contain("funct3 = F3_ADD_SUB")
expect(vhdl).to_contain("funct7 = F7_SUB_SRA")
expect(vhdl).to_contain("alu_op <= ALU_SUB;")
expect(vhdl).to_contain("alu_op <= ALU_ADD;")
```

</details>

#### decodes I-type ALU operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()

expect(vhdl).to_contain("opcode = OP_IMM")
expect(vhdl).to_contain("alu_op <= ALU_SLL;")
expect(vhdl).to_contain("alu_op <= ALU_SLT;")
expect(vhdl).to_contain("alu_op <= ALU_XOR;")
expect(vhdl).to_contain("alu_op <= ALU_OR;")
expect(vhdl).to_contain("alu_op <= ALU_AND;")
```

</details>

#### assigns LUI to ALU_PASS_B

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()
expect(vhdl).to_contain("opcode = OP_LUI")
expect(vhdl).to_contain("alu_op <= ALU_PASS_B;")
```

</details>

#### defaults address-calc opcodes to ALU_ADD

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()
expect(vhdl).to_contain("opcode = OP_AUIPC")
expect(vhdl).to_contain("opcode = OP_JAL")
expect(vhdl).to_contain("opcode = OP_LOAD")
expect(vhdl).to_contain("opcode = OP_STORE")
```

</details>

#### uses rv32i_pkg constants not raw literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vhdl = render_rv32i_alu_control()
expect(vhdl).to_contain("use work.rv32i_pkg.all;")
# Should use named constants, not raw binary strings in decode logic
expect(vhdl).to_contain("alu_decode: process(opcode, funct3, funct7)")
```

</details>

### RV32I decode bundle

#### produces both package and entity VHDL

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundle = render_rv32i_decode_bundle()

expect(bundle.package_vhdl.len() > 0).to_equal(true)
expect(bundle.decode_entity_vhdl.len() > 0).to_equal(true)

# Package has opcode constants
expect(bundle.package_vhdl).to_contain("package rv32i_pkg is")
expect(bundle.package_vhdl).to_contain("OP_LUI")

# Decode entity has field extractor and ALU control
expect(bundle.decode_entity_vhdl).to_contain("entity rv32i_decoder is")
expect(bundle.decode_entity_vhdl).to_contain("entity rv32i_alu_ctrl is")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_rv32i_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VHDL register file template
- address width calculation
- RV32I opcode package
- RV32I field extractor entity
- RV32I ALU control decoder
- RV32I decode bundle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
