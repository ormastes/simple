# Hwir Mir Function Extract Specification

> Tests covering strict HWIR real MIR extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 55 | 55 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hwir Mir Function Extract Specification

## Scenarios

### strict HWIR real MIR extraction

#### should extract every closed RV64-only Zca row intrinsic without fallback

- should extract every closed RV64-only Zca row intrinsic without fallback
- Lower each declared RV64-only Zca intrinsic through the strict real-MIR boundary
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.config.xlen equals `64`
   - Expected: has_origin_source(module, origin_ids[index]) is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract every closed RV64-only Zca row intrinsic without fallback")
step("Lower each declared RV64-only Zca intrinsic through the strict real-MIR boundary")
val intrinsic_ids = ["__simple_riscv_zca_cld_rv64_row_v1", "__simple_riscv_zca_csd_rv64_row_v1",
    "__simple_riscv_zca_ldsp_rv64_row_v1", "__simple_riscv_zca_sdsp_rv64_row_v1",
    "__simple_riscv_zca_caddw_rv64_row_v1", "__simple_riscv_zca_csubw_rv64_row_v1",
    "__simple_riscv_zca_slli6_rv64_row_v1", "__simple_riscv_zca_srli6_rv64_row_v1",
    "__simple_riscv_zca_srai6_rv64_row_v1"]
val origin_ids = ["zca.rv64.c.ld", "zca.rv64.c.sd", "zca.rv64.c.ldsp", "zca.rv64.c.sdsp",
    "zca.rv64.c.addw", "zca.rv64.c.subw", "zca.rv64.c.slli6", "zca.rv64.c.srli6",
    "zca.rv64.c.srai6"]
var index = 0
for intrinsic_id in intrinsic_ids:
    val result = lower_strict_mir_function_to_hwir(
        hardware_rv64_zca_row_intrinsic_function(intrinsic_id, "mir_rv64_zca_" + index.to_text()),
        CoreConfig.rv64_zca_mission_critical())
    expect(result.is_success()).to_equal(true)
    expect(result.uses_legacy_fallback()).to_equal(false)
    if val module = result.module:
        expect(module.config.xlen).to_equal(64)
        expect(has_origin_source(module, origin_ids[index])).to_equal(true)
    else:
        expect(false).to_equal(true)
    index = index + 1
```

</details>

#### should reject every closed RV64-only Zca row intrinsic for RV32 elaboration

- should reject every closed RV64-only Zca row intrinsic for RV32 elaboration
- Present each RV64-only intrinsic to the RV32 strict-lowering configuration
   - Expected: result.is_success() is false
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject every closed RV64-only Zca row intrinsic for RV32 elaboration")
step("Present each RV64-only intrinsic to the RV32 strict-lowering configuration")
val intrinsic_ids = ["__simple_riscv_zca_cld_rv64_row_v1", "__simple_riscv_zca_csd_rv64_row_v1",
    "__simple_riscv_zca_ldsp_rv64_row_v1", "__simple_riscv_zca_sdsp_rv64_row_v1",
    "__simple_riscv_zca_caddw_rv64_row_v1", "__simple_riscv_zca_csubw_rv64_row_v1",
    "__simple_riscv_zca_slli6_rv64_row_v1", "__simple_riscv_zca_srli6_rv64_row_v1",
    "__simple_riscv_zca_srai6_rv64_row_v1"]
for intrinsic_id in intrinsic_ids:
    val result = lower_strict_mir_function_to_hwir(
        hardware_rv64_zca_row_intrinsic_function(intrinsic_id, "mir_rv32_reject"),
        CoreConfig.rv32_zca_mission_critical())
    expect(result.is_success()).to_equal(false)
    expect(result.diagnostic).to_contain("RV64")
    expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject malformed and prefix-lookalike RV64 Zca intrinsics at the closed boundary

- should reject malformed and prefix-lookalike RV64 Zca intrinsics at the closed boundary
- Vary operands, result flow, and intrinsic identity at the closed RV64 boundary
   - Expected: missing_result.is_success() is false
   - Expected: return_result.is_success() is false
   - Expected: lookalike.is_success() is false
   - Expected: lookalike.diagnostic equals `HWIR-E-MIR-INTRINSIC: strict RV64 Zca intrinsic is absent from the closed con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject malformed and prefix-lookalike RV64 Zca intrinsics at the closed boundary")
step("Vary operands, result flow, and intrinsic identity at the closed RV64 boundary")
var missing_operand = hardware_rv64_zca_row_intrinsic_function(
    "__simple_riscv_zca_cld_rv64_row_v1", "mir_rv64_missing_operand")
missing_operand = with_entry_instruction(missing_operand, MirInst(kind: MirInstKind.Intrinsic(
    Some(LocalId(id: 1)), "__simple_riscv_zca_cld_rv64_row_v1", []), span: nil))
val missing_result = lower_strict_mir_function_to_hwir(missing_operand, CoreConfig.rv64_zca_mission_critical())
expect(missing_result.is_success()).to_equal(false)
expect(missing_result.diagnostic).to_contain("one u32 parcel semantic operand")
var wrong_return = hardware_rv64_zca_row_intrinsic_function(
    "__simple_riscv_zca_csd_rv64_row_v1", "mir_rv64_wrong_return")
wrong_return = with_block_terminator(wrong_return, 0, MirTerminator.Ret(Some(copy(0))))
val return_result = lower_strict_mir_function_to_hwir(wrong_return, CoreConfig.rv64_zca_mission_critical())
expect(return_result.is_success()).to_equal(false)
expect(return_result.diagnostic).to_contain("must return the semantic result")
val lookalike = lower_strict_mir_function_to_hwir(
    hardware_rv64_zca_row_intrinsic_function("__simple_riscv_zca_cld_extra_rv64_row_v1", "mir_rv64_lookalike"),
    CoreConfig.rv64_zca_mission_critical())
expect(lookalike.is_success()).to_equal(false)
expect(lookalike.diagnostic).to_equal("HWIR-E-MIR-INTRINSIC: strict RV64 Zca intrinsic is absent from the closed contract")
```

</details>

#### should extract the real Bool BitAnd and its MIR origins

- should extract the real Bool BitAnd and its MIR origins
- Lower a boolean real-MIR function and inspect its typed origins and strict rendering
   - Expected: result.is_success() is true
   - Expected: module.ports[0].name equals `a`
   - Expected: module.ports[0].bit_width equals `1`
   - Expected: module.comb_ops[0].op equals `and`
   - Expected: module.origins[0].source_name equals `mir.local.0`
   - Expected: module.origins[2].node_id.value equals `mir_bool_and:bitwise`
   - Expected: module.origins[2].source_name equals `mir.block.0`
   - Expected: emitted.is_success() is true
   - Expected: emitted.route equals `hwir-strict`
   - Expected: emitted.module_node_id equals `mir_bool_and:module`
   - Expected: emitted.config_xlen equals `64`
   - Expected: emitted.vhdl.starts_with("-- simple-hwir route=hwir-strict") is true
   - Expected: emitted.vhdl contains `result_out <= a and b;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the real Bool BitAnd and its MIR origins")
step("Lower a boolean real-MIR function and inspect its typed origins and strict rendering")
val result = lower_strict_mir_function_to_hwir(hardware_and_function(), CoreConfig.rv64())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.ports[0].name).to_equal("a")
    expect(module.ports[0].bit_width).to_equal(1)
    expect(module.comb_ops[0].op).to_equal("and")
    expect(module.origins[0].source_name).to_equal("mir.local.0")
    expect(module.origins[2].node_id.value).to_equal("mir_bool_and:bitwise")
    expect(module.origins[2].source_name).to_equal("mir.block.0")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.route).to_equal("hwir-strict")
    expect(emitted.module_node_id).to_equal("mir_bool_and:module")
    expect(emitted.config_xlen).to_equal(64)
    expect(emitted.vhdl.starts_with("-- simple-hwir route=hwir-strict")).to_equal(true)
    expect(emitted.vhdl.contains("result_out <= a and b;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a fixed-width u32 BitAnd without using XLEN for datapath width

- should extract a fixed-width u32 BitAnd without using XLEN for datapath width
- Lower a u32 BitAnd under an RV64 configuration and inspect the fixed datapath width
   - Expected: result.is_success() is true
   - Expected: module.config.xlen equals `64`
   - Expected: module.ports[0].bit_width equals `32`
   - Expected: module.comb_ops[0].bit_width equals `32`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `a : in std_logic_vector(31 downto 0)`
   - Expected: emitted.vhdl contains `result_out <= a and b;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a fixed-width u32 BitAnd without using XLEN for datapath width")
step("Lower a u32 BitAnd under an RV64 configuration and inspect the fixed datapath width")
val result = lower_strict_mir_function_to_hwir(hardware_u32_and_function(), CoreConfig.rv64())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.config.xlen).to_equal(64)
    expect(module.ports[0].bit_width).to_equal(32)
    expect(module.comb_ops[0].bit_width).to_equal(32)
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("a : in std_logic_vector(31 downto 0)")).to_equal(true)
    expect(emitted.vhdl.contains("result_out <= a and b;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a fixed-width u32 BitOr for instruction assembly

- should extract a fixed-width u32 BitOr for instruction assembly
- Lower a u32 BitOr instruction-assembly fixture through strict HWIR
   - Expected: result.is_success() is true
   - Expected: module.comb_ops[0].op equals `or`
   - Expected: module.comb_ops[0].bit_width equals `32`
   - Expected: emitted.vhdl contains `result_out <= a or b;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a fixed-width u32 BitOr for instruction assembly")
step("Lower a u32 BitOr instruction-assembly fixture through strict HWIR")
var mir_function = hardware_u32_and_function()
mir_function.name = "mir_u32_or"
mir_function = with_entry_instruction(mir_function, MirInst(kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.BitOr, copy(0), copy(1)), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.comb_ops[0].op).to_equal("or")
    expect(module.comb_ops[0].bit_width).to_equal(32)
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.vhdl.contains("result_out <= a or b;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a real typed u32 parcel mask constant graph

- should extract a real typed u32 parcel mask constant graph
- Lower the typed parcel-mask constant graph and inspect its strict HWIR shape
   - Expected: result.is_success() is true
   - Expected: module.ports.len() equals `2`
   - Expected: module.ports[0].name equals `parcel`
   - Expected: module.ports[0].bit_width equals `32`
   - Expected: module.constants.len() equals `1`
   - Expected: module.constants[0].value equals `65535`
   - Expected: module.comb_ops[0].rhs equals `mask`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `constant mask : std_logic_vector(31 downto 0) := "000000000000000011111111111... (full value in folded executable source)`
   - Expected: emitted.vhdl contains `masked <= parcel and mask;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a real typed u32 parcel mask constant graph")
step("Lower the typed parcel-mask constant graph and inspect its strict HWIR shape")
val result = lower_strict_mir_function_to_hwir(hardware_u32_parcel_mask_function(), CoreConfig.rv64_zca_integer())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.ports.len()).to_equal(2)
    expect(module.ports[0].name).to_equal("parcel")
    expect(module.ports[0].bit_width).to_equal(32)
    expect(module.constants.len()).to_equal(1)
    expect(module.constants[0].value).to_equal(65535)
    expect(module.comb_ops[0].rhs).to_equal("mask")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("constant mask : std_logic_vector(31 downto 0) := \"00000000000000001111111111111111\";")).to_equal(true)
    expect(emitted.vhdl.contains("masked <= parcel and mask;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a real typed bounded parcel shift graph

- should extract a real typed bounded parcel shift graph
- Lower the bounded parcel right-shift graph through strict HWIR
   - Expected: result.is_success() is true
   - Expected: module.constants[0].name equals `shift`
   - Expected: module.constants[0].value equals `13`
   - Expected: module.comb_ops[0].op equals `shr`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `shifted <= (others => '0') when unsigned(shift) >= to_unsigned(32, 32)`
   - Expected: emitted.vhdl contains `shift_right(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a real typed bounded parcel shift graph")
step("Lower the bounded parcel right-shift graph through strict HWIR")
val result = lower_strict_mir_function_to_hwir(hardware_u32_parcel_shift_function(), CoreConfig.rv64_zca_integer())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.constants[0].name).to_equal("shift")
    expect(module.constants[0].value).to_equal(13)
    expect(module.comb_ops[0].op).to_equal("shr")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("shifted <= (others => '0') when unsigned(shift) >= to_unsigned(32, 32)")).to_equal(true)
    expect(emitted.vhdl.contains("shift_right(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a real typed bounded left shift for canonical instruction fields

- should extract a real typed bounded left shift for canonical instruction fields
- Lower the bounded left-shift instruction-field graph through strict HWIR
   - Expected: result.is_success() is true
   - Expected: module.comb_ops[0].op equals `shl`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `shifted <= (others => '0') when unsigned(shift) >= to_unsigned(32, 32)`
   - Expected: emitted.vhdl contains `shift_left(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a real typed bounded left shift for canonical instruction fields")
step("Lower the bounded left-shift instruction-field graph through strict HWIR")
var mir_function = hardware_u32_parcel_shift_function()
mir_function.name = "mir_u32_canonical_field_shift"
mir_function = with_block_instruction(mir_function, 0, 1, MirInst(kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.Shl, copy(0), copy(1)), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.comb_ops[0].op).to_equal("shl")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("shifted <= (others => '0') when unsigned(shift) >= to_unsigned(32, 32)")).to_equal(true)
    expect(emitted.vhdl.contains("shift_left(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract a real two-stage parcel field graph through an internal signal

- should extract a real two-stage parcel field graph through an internal signal
- Lower the internal-signal parcel-field graph through strict HWIR
   - Expected: result.is_success() is true
   - Expected: module.signals.len() equals `2`
   - Expected: module.signals[0].name equals `shifted`
   - Expected: module.constants.len() equals `2`
   - Expected: module.comb_ops.len() equals `3`
   - Expected: module.comb_ops[0].result equals `shifted`
   - Expected: module.comb_ops[1].lhs equals `shifted`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `signal shifted : std_logic_vector(31 downto 0);`
   - Expected: emitted.vhdl contains `shift_right(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))`
   - Expected: emitted.vhdl contains `field <= shifted and mask;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract a real two-stage parcel field graph through an internal signal")
step("Lower the internal-signal parcel-field graph through strict HWIR")
val result = lower_strict_mir_function_to_hwir(hardware_u32_parcel_field_function(), CoreConfig.rv32_zca_integer())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.signals.len()).to_equal(2)
    expect(module.signals[0].name).to_equal("shifted")
    expect(module.constants.len()).to_equal(2)
    expect(module.comb_ops.len()).to_equal(3)
    expect(module.comb_ops[0].result).to_equal("shifted")
    expect(module.comb_ops[1].lhs).to_equal("shifted")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("signal shifted : std_logic_vector(31 downto 0);")).to_equal(true)
    expect(emitted.vhdl.contains("shift_right(unsigned(parcel), to_integer(unsigned(shift(4 downto 0))))")).to_equal(true)
    expect(emitted.vhdl.contains("field <= shifted and mask;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the C.EBREAK canonical instruction constant leaf

- should extract the C.EBREAK canonical instruction constant leaf
- Lower the C.EBREAK canonical instruction constant fixture
   - Expected: result.is_success() is true
   - Expected: module.ports[0].name equals `canonical_instruction`
   - Expected: module.constants[0].value equals `0x00100073`
   - Expected: module.comb_ops[0].op equals `passthrough`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `canonical_instruction <= canonical_value;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the C.EBREAK canonical instruction constant leaf")
step("Lower the C.EBREAK canonical instruction constant fixture")
val result = lower_strict_mir_function_to_hwir(hardware_cebreak_canonical_function(), CoreConfig.rv32_zca_integer())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.ports[0].name).to_equal("canonical_instruction")
    expect(module.constants[0].value).to_equal(0x00100073)
    expect(module.comb_ops[0].op).to_equal("passthrough")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("canonical_instruction <= canonical_value;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the frontend-style C.EBREAK match, select, and joined return

- should extract the frontend-style C.EBREAK match, select, and joined return
- Lower the C.EBREAK branch and joined-return real-MIR fixture
   - Expected: result.is_success() is true
   - Expected: module.config.compressed_decode_profile equals `zca-common-critical`
   - Expected: module.signals[0].name equals `is_cebreak`
   - Expected: module.signals[0].bit_width equals `1`
   - Expected: module.compare_ops.len() equals `1`
   - Expected: module.compare_ops[0].lhs equals `parcel`
   - Expected: module.compare_ops[0].rhs equals `cebreak_parcel`
   - Expected: module.select_ops.len() equals `1`
   - Expected: module.select_ops[0].condition equals `is_cebreak`
   - Expected: module.select_ops[0].when_true equals `canonical_ebreak`
   - Expected: module.select_ops[0].when_false equals `illegal_instruction`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `is_cebreak <= '1' when parcel = cebreak_parcel else '0';`
   - Expected: emitted.vhdl contains `canonical_instruction <= canonical_ebreak when is_cebreak = '1' else illegal_... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the frontend-style C.EBREAK match, select, and joined return")
step("Lower the C.EBREAK branch and joined-return real-MIR fixture")
val result = lower_strict_mir_function_to_hwir(hardware_cebreak_decode_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.config.compressed_decode_profile).to_equal("zca-common-critical")
    expect(module.signals[0].name).to_equal("is_cebreak")
    expect(module.signals[0].bit_width).to_equal(1)
    expect(module.compare_ops.len()).to_equal(1)
    expect(module.compare_ops[0].lhs).to_equal("parcel")
    expect(module.compare_ops[0].rhs).to_equal("cebreak_parcel")
    expect(module.select_ops.len()).to_equal(1)
    expect(module.select_ops[0].condition).to_equal("is_cebreak")
    expect(module.select_ops[0].when_true).to_equal("canonical_ebreak")
    expect(module.select_ops[0].when_false).to_equal("illegal_instruction")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("is_cebreak <= '1' when parcel = cebreak_parcel else '0';")).to_equal(true)
    expect(emitted.vhdl.contains("canonical_instruction <= canonical_ebreak when is_cebreak = '1' else illegal_instruction;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract C.NOP through the shared C.ADDI/C.NOP semantic row

- should extract C.NOP through the shared C.ADDI/C.NOP semantic row
- Lower the shared C.ADDI/C.NOP semantic-row fixture
   - Expected: result.is_success() is true
   - Expected: module.config.xlen equals `64`
   - Expected: module.origins[0].source_name equals `zca.c.nop_addi`
   - Expected: module.signals[2].name equals `is_c_addi`
   - Expected: module.constants[2].value equals `1`
   - Expected: module.select_ops[1].when_false equals `zero_instruction`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `is_c_addi <= '1' when opcode_tag = c_addi_tag else '0';`
   - Expected: emitted.vhdl contains `constant addi_opcode : std_logic_vector(31 downto 0) := "00000000000000000000... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract C.NOP through the shared C.ADDI/C.NOP semantic row")
step("Lower the shared C.ADDI/C.NOP semantic-row fixture")
var mir_function = hardware_cebreak_decode_function()
mir_function.name = "mir_cnop_decode"
mir_function = with_block_instruction(mir_function, 0, 0, MirInst(kind: MirInstKind.Const(LocalId(id: 1), MirConstValue.Int(1), u32_type()), span: nil))
mir_function = with_block_instruction(mir_function, 1, 0, MirInst(kind: MirInstKind.Const(LocalId(id: 3), MirConstValue.Int(19), u32_type()), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv64_zca_mission_critical())
expect(result.is_success()).to_equal(true)
if val module = result.module:
    expect(module.config.xlen).to_equal(64)
    expect(module.origins[0].source_name).to_equal("zca.c.nop_addi")
    expect(module.signals[2].name).to_equal("is_c_addi")
    expect(module.constants[2].value).to_equal(1)
    expect(module.select_ops[1].when_false).to_equal("zero_instruction")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("is_c_addi <= '1' when opcode_tag = c_addi_tag else '0';")).to_equal(true)
    expect(emitted.vhdl.contains("constant addi_opcode : std_logic_vector(31 downto 0) := \"00000000000000000000000000010011\";")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.LI semantic intrinsic without fallback

- should extract the reserved real-MIR C.LI semantic intrinsic without fallback
- Lower the declared C.LI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.li`
   - Expected: module.config.compressed_decode_profile equals `zca-common-critical`
   - Expected: module.select_ops[1].condition equals `is_c_li`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.LI semantic intrinsic without fallback")
step("Lower the declared C.LI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cli_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.li")
    expect(module.config.compressed_decode_profile).to_equal("zca-common-critical")
    expect(module.select_ops[1].condition).to_equal("is_c_li")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a malformed C.LI semantic intrinsic before HWIR emission

- should reject a malformed C.LI semantic intrinsic before HWIR emission
- Submit a malformed C.LI intrinsic before strict HWIR emission
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-INTRINSIC: strict C.LI lowering requires the reserved parcel seman... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a malformed C.LI semantic intrinsic before HWIR emission")
step("Submit a malformed C.LI intrinsic before strict HWIR emission")
var mir_function = hardware_cli_intrinsic_function()
mir_function = with_entry_instruction(mir_function, MirInst(kind: MirInstKind.Intrinsic(Some(LocalId(id: 1)), "__simple_riscv_zca_cli_row_v1", []), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-INTRINSIC: strict C.LI lowering requires the reserved parcel semantic intrinsic")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a reserved-looking Zca intrinsic absent from the canonical contract

- should reject a reserved-looking Zca intrinsic absent from the canonical contract
- Submit an undeclared reserved-looking intrinsic to the closed contract
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-INTRINSIC: strict Zca intrinsic is absent from the canonical contract`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a reserved-looking Zca intrinsic absent from the canonical contract")
step("Submit an undeclared reserved-looking intrinsic to the closed contract")
var mir_function = hardware_cli_intrinsic_function()
mir_function = with_entry_instruction(mir_function, MirInst(kind: MirInstKind.Intrinsic(Some(LocalId(id: 1)), "__simple_riscv_zca_unproven_row_v1", [copy(0)]), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-INTRINSIC: strict Zca intrinsic is absent from the canonical contract")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should extract the reserved real-MIR C.ADDI/C.NOP semantic intrinsic without fallback

- should extract the reserved real-MIR C.ADDI/C.NOP semantic intrinsic without fallback
- Lower the declared C.ADDI/C.NOP semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.nop_addi`
   - Expected: module.config.compressed_decode_profile equals `zca-common-critical`
   - Expected: module.summary.comb_op_count equals `20`
   - Expected: module.select_ops[1].condition equals `is_c_addi`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `canonical_instruction <= addi_instruction when is_c_addi = '1' else zero_inst... (full value in folded executable source)`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.ADDI/C.NOP semantic intrinsic without fallback")
step("Lower the declared C.ADDI/C.NOP semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_caddi_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.nop_addi")
    expect(module.config.compressed_decode_profile).to_equal("zca-common-critical")
    expect(module.summary.comb_op_count).to_equal(20)
    expect(module.select_ops[1].condition).to_equal("is_c_addi")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("canonical_instruction <= addi_instruction when is_c_addi = '1' else zero_instruction;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.ADDI16SP semantic intrinsic without fallback

- should extract the reserved real-MIR C.ADDI16SP semantic intrinsic without fallback
- Lower the declared C.ADDI16SP semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.addi16sp`
   - Expected: module.summary.comb_op_count equals `36`
   - Expected: module.select_ops[3].condition equals `imm_is_zero`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `caddi16sp_if_rd <= caddi16sp_if_tag when rd_is_sp = '1' else zero_instruction;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.ADDI16SP semantic intrinsic without fallback")
step("Lower the declared C.ADDI16SP semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_caddi16sp_intrinsic_function(), CoreConfig.rv64_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.addi16sp")
    expect(module.summary.comb_op_count).to_equal(36)
    expect(module.select_ops[3].condition).to_equal("imm_is_zero")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("caddi16sp_if_rd <= caddi16sp_if_tag when rd_is_sp = '1' else zero_instruction;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.LUI semantic intrinsic without fallback

- should extract the reserved real-MIR C.LUI semantic intrinsic without fallback
- Lower the declared C.LUI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.lui`
   - Expected: module.summary.comb_op_count equals `23`
   - Expected: module.select_ops[4].condition equals `imm_is_zero`
   - Expected: emitted.is_success() is true
   - Expected: emitted.vhdl contains `clui_if_rdsp <= zero_instruction when rd_is_sp = '1' else clui_if_rd0;`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.LUI semantic intrinsic without fallback")
step("Lower the declared C.LUI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_clui_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.lui")
    expect(module.summary.comb_op_count).to_equal(23)
    expect(module.select_ops[4].condition).to_equal("imm_is_zero")
    val emitted = render_strict_hwir_vhdl(module)
    expect(emitted.is_success()).to_equal(true)
    expect(emitted.vhdl.contains("clui_if_rdsp <= zero_instruction when rd_is_sp = '1' else clui_if_rd0;")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a C.ADDI semantic intrinsic with a non-semantic return

- should reject a C.ADDI semantic intrinsic with a non-semantic return
- Return a non-semantic value from the C.ADDI intrinsic fixture
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-RETURN: strict C.ADDI intrinsic lowering must return the semantic ... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a C.ADDI semantic intrinsic with a non-semantic return")
step("Return a non-semantic value from the C.ADDI intrinsic fixture")
var mir_function = hardware_caddi_intrinsic_function()
mir_function = with_block_terminator(mir_function, 0, MirTerminator.Ret(Some(copy(0))))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-RETURN: strict C.ADDI intrinsic lowering must return the semantic result")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should extract the reserved real-MIR C.ADDI4SPN semantic intrinsic without fallback

- should extract the reserved real-MIR C.ADDI4SPN semantic intrinsic without fallback
- Lower the declared C.ADDI4SPN semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.addi4spn`
   - Expected: module.config.xlen equals `64`
   - Expected: module.summary.comb_op_count equals `29`
   - Expected: module.select_ops[1].condition equals `is_c_addi4spn`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.ADDI4SPN semantic intrinsic without fallback")
step("Lower the declared C.ADDI4SPN semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_addi4spn_intrinsic_function(), CoreConfig.rv64_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.addi4spn")
    expect(module.config.xlen).to_equal(64)
    expect(module.summary.comb_op_count).to_equal(29)
    expect(module.select_ops[1].condition).to_equal("is_c_addi4spn")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.LW semantic intrinsic without fallback

- should extract the reserved real-MIR C.LW semantic intrinsic without fallback
- Lower the declared C.LW semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.lw`
   - Expected: module.summary.comb_op_count equals `28`
   - Expected: module.select_ops[0].condition equals `is_c_lw`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.LW semantic intrinsic without fallback")
step("Lower the declared C.LW semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_lw_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.lw")
    expect(module.summary.comb_op_count).to_equal(28)
    expect(module.select_ops[0].condition).to_equal("is_c_lw")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.SW semantic intrinsic without fallback

- should extract the reserved real-MIR C.SW semantic intrinsic without fallback
- Lower the declared C.SW semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.sw`
   - Expected: module.summary.comb_op_count equals `32`
   - Expected: module.select_ops[0].condition equals `is_c_sw`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.SW semantic intrinsic without fallback")
step("Lower the declared C.SW semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_sw_intrinsic_function(), CoreConfig.rv64_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.sw")
    expect(module.summary.comb_op_count).to_equal(32)
    expect(module.select_ops[0].condition).to_equal("is_c_sw")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.LWSP semantic intrinsic without fallback

- should extract the reserved real-MIR C.LWSP semantic intrinsic without fallback
- Lower the declared C.LWSP semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.lwsp`
   - Expected: module.summary.comb_op_count equals `26`
   - Expected: module.select_ops[1].condition equals `is_c_lwsp`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.LWSP semantic intrinsic without fallback")
step("Lower the declared C.LWSP semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_lwsp_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.lwsp")
    expect(module.summary.comb_op_count).to_equal(26)
    expect(module.select_ops[1].condition).to_equal("is_c_lwsp")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.SWSP semantic intrinsic without fallback

- should extract the reserved real-MIR C.SWSP semantic intrinsic without fallback
- Lower the declared C.SWSP semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.swsp`
   - Expected: module.summary.comb_op_count equals `23`
   - Expected: module.select_ops[0].condition equals `is_c_swsp`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.SWSP semantic intrinsic without fallback")
step("Lower the declared C.SWSP semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_swsp_intrinsic_function(), CoreConfig.rv64_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.swsp")
    expect(module.summary.comb_op_count).to_equal(23)
    expect(module.select_ops[0].condition).to_equal("is_c_swsp")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR five-bit C.SLLI semantic intrinsic without fallback

- should extract the reserved real-MIR five-bit C.SLLI semantic intrinsic without fallback
- Lower the declared five-bit C.SLLI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.slli.low`
   - Expected: module.summary.comb_op_count equals `15`
   - Expected: module.select_ops[0].condition equals `is_c_slli_low`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR five-bit C.SLLI semantic intrinsic without fallback")
step("Lower the declared five-bit C.SLLI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_slli_low_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.slli.low")
    expect(module.summary.comb_op_count).to_equal(15)
    expect(module.select_ops[0].condition).to_equal("is_c_slli_low")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR five-bit C.SRLI semantic intrinsic without fallback

- should extract the reserved real-MIR five-bit C.SRLI semantic intrinsic without fallback
- Lower the declared five-bit C.SRLI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.srli.low`
   - Expected: module.summary.comb_op_count equals `16`
   - Expected: module.select_ops[0].condition equals `is_c_srli_low`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR five-bit C.SRLI semantic intrinsic without fallback")
step("Lower the declared five-bit C.SRLI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_srli_low_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.srli.low")
    expect(module.summary.comb_op_count).to_equal(16)
    expect(module.select_ops[0].condition).to_equal("is_c_srli_low")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR five-bit C.SRAI semantic intrinsic without fallback

- should extract the reserved real-MIR five-bit C.SRAI semantic intrinsic without fallback
- Lower the declared five-bit C.SRAI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.srai.low`
   - Expected: module.summary.comb_op_count equals `17`
   - Expected: module.select_ops[0].condition equals `is_c_srai_low`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR five-bit C.SRAI semantic intrinsic without fallback")
step("Lower the declared five-bit C.SRAI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_srai_low_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.srai.low")
    expect(module.summary.comb_op_count).to_equal(17)
    expect(module.select_ops[0].condition).to_equal("is_c_srai_low")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.ANDI semantic intrinsic without fallback

- should extract the reserved real-MIR C.ANDI semantic intrinsic without fallback
- Lower the declared C.ANDI semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.andi`
   - Expected: module.summary.comb_op_count equals `22`
   - Expected: module.select_ops[1].condition equals `is_c_andi`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.ANDI semantic intrinsic without fallback")
step("Lower the declared C.ANDI semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_candi_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.andi")
    expect(module.summary.comb_op_count).to_equal(22)
    expect(module.select_ops[1].condition).to_equal("is_c_andi")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.SUB semantic intrinsic without fallback

- should extract the reserved real-MIR C.SUB semantic intrinsic without fallback
- Lower the declared C.SUB semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.sub`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_sub`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.SUB semantic intrinsic without fallback")
step("Lower the declared C.SUB semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_csub_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.sub")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_sub")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.XOR semantic intrinsic without fallback

- should extract the reserved real-MIR C.XOR semantic intrinsic without fallback
- Lower the declared C.XOR semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.xor`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_xor`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.XOR semantic intrinsic without fallback")
step("Lower the declared C.XOR semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cxor_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.xor")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_xor")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.OR semantic intrinsic without fallback

- should extract the reserved real-MIR C.OR semantic intrinsic without fallback
- Lower the declared C.OR semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.or`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_or`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.OR semantic intrinsic without fallback")
step("Lower the declared C.OR semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cor_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.or")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_or")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.AND semantic intrinsic without fallback

- should extract the reserved real-MIR C.AND semantic intrinsic without fallback
- Lower the declared C.AND semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.and`
   - Expected: module.summary.comb_op_count equals `18`
   - Expected: module.select_ops[0].condition equals `is_c_and`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.AND semantic intrinsic without fallback")
step("Lower the declared C.AND semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cand_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.and")
    expect(module.summary.comb_op_count).to_equal(18)
    expect(module.select_ops[0].condition).to_equal("is_c_and")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.JR semantic intrinsic without fallback

- should extract the reserved real-MIR C.JR semantic intrinsic without fallback
- Lower the declared C.JR semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.jr`
   - Expected: module.summary.comb_op_count equals `10`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.JR semantic intrinsic without fallback")
step("Lower the declared C.JR semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cjr_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.jr")
    expect(module.summary.comb_op_count).to_equal(10)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the real-MIR C.MV semantic intrinsic without fallback

- should extract the real-MIR C.MV semantic intrinsic without fallback
- Lower the declared C.MV semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.mv`
   - Expected: module.summary.comb_op_count equals `16`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: module.select_ops[2].condition equals `rs2_is_zero`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the real-MIR C.MV semantic intrinsic without fallback")
step("Lower the declared C.MV semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cmv_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.mv")
    expect(module.summary.comb_op_count).to_equal(16)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(module.select_ops[2].condition).to_equal("rs2_is_zero")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the reserved real-MIR C.JALR semantic intrinsic without fallback

- should extract the reserved real-MIR C.JALR semantic intrinsic without fallback
- Lower the declared C.JALR semantic intrinsic without a fallback route
   - Expected: result.is_success() is true
   - Expected: result.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.jalr`
   - Expected: module.summary.comb_op_count equals `11`
   - Expected: module.select_ops[1].condition equals `rd_is_zero`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the reserved real-MIR C.JALR semantic intrinsic without fallback")
step("Lower the declared C.JALR semantic intrinsic without a fallback route")
val result = lower_strict_mir_function_to_hwir(hardware_cjalr_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(true)
expect(result.uses_legacy_fallback()).to_equal(false)
if val module = result.module:
    expect(module.origins[0].source_name).to_equal("zca.c.jalr")
    expect(module.summary.comb_op_count).to_equal(11)
    expect(module.select_ops[1].condition).to_equal("rd_is_zero")
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should extract the aggregate real-MIR C.J predecode intrinsic without fallback

- should extract the aggregate real-MIR C.J predecode intrinsic without fallback
- Lower the aggregate C.J predecode intrinsic through strict HWIR
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.uses_legacy_fallback() is false
   - Expected: module32.origins[3].source_name equals `zca.c.j`
   - Expected: module32.port_width("original_parcel") equals `16`
   - Expected: module32.port_width("next_pc") equals `32`
   - Expected: render_strict_hwir_vhdl(module32).is_success() is true
   - Expected: false is true
   - Expected: module64.port_width("fetch_pc") equals `56`
   - Expected: module64.port_width("redirect_target") equals `56`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract the aggregate real-MIR C.J predecode intrinsic without fallback")
step("Lower the aggregate C.J predecode intrinsic through strict HWIR")
val rv32 = lower_strict_mir_function_to_hwir(hardware_cj_predecode_intrinsic_function(32), CoreConfig.rv32_zca_mission_critical())
val rv64 = lower_strict_mir_function_to_hwir(hardware_cj_predecode_intrinsic_function(56), CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.uses_legacy_fallback()).to_equal(false)
if val module32 = rv32.module:
    expect(module32.origins[3].source_name).to_equal("zca.c.j")
    expect(module32.port_width("original_parcel")).to_equal(16)
    expect(module32.port_width("next_pc")).to_equal(32)
    expect(render_strict_hwir_vhdl(module32).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
if val module64 = rv64.module:
    expect(module64.port_width("fetch_pc")).to_equal(56)
    expect(module64.port_width("redirect_target")).to_equal(56)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject an aggregate C.J predecode MIR signature with a non-Bits PC

- should reject an aggregate C.J predecode MIR signature with a non-Bits PC
- Submit a C.J predecode signature with a non-Bits program counter
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-SIGNATURE: strict C.J predecode lowering requires Bits[16], Bits[P... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject an aggregate C.J predecode MIR signature with a non-Bits PC")
step("Submit a C.J predecode signature with a non-Bits program counter")
var mir_function = hardware_cj_predecode_intrinsic_function(32)
mir_function.signature = MirSignature(params: [bits_type(16), u32_type()],
    return_type: cj_predecode_result_type(32), is_variadic: false)
val cj_pc_local = mir_function.locals[1]
cj_pc_local.type_ = u32_type()
mir_function.locals[1] = cj_pc_local
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-SIGNATURE: strict C.J predecode lowering requires Bits[16], Bits[PA] -> (Bits[32], Bits[2], Bool, Bits[PA], Bool, Bits[PA])")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should extract aggregate C.BEQZ/C.BNEZ real-MIR predecode intrinsics without fallback

- should extract aggregate C.BEQZ/C.BNEZ real-MIR predecode intrinsics without fallback
- Lower the aggregate C.BEQZ and C.BNEZ predecode intrinsics
   - Expected: beqz.is_success() is true
   - Expected: bnez.is_success() is true
   - Expected: beqz.uses_legacy_fallback() is false
   - Expected: bnez.uses_legacy_fallback() is false
   - Expected: module.origins[0].source_name equals `zca.c.beqz`
   - Expected: module.port_width("rs1_value") equals `32`
   - Expected: module.port_width("next_pc") equals `32`
   - Expected: render_strict_hwir_vhdl(module).is_success() is true
   - Expected: false is true
   - Expected: module.origins[0].source_name equals `zca.c.bnez`
   - Expected: module.port_width("rs1_value") equals `64`
   - Expected: module.port_width("redirect_target") equals `56`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract aggregate C.BEQZ/C.BNEZ real-MIR predecode intrinsics without fallback")
step("Lower the aggregate C.BEQZ and C.BNEZ predecode intrinsics")
val beqz = lower_strict_mir_function_to_hwir(
    hardware_cb_predecode_intrinsic_function(32, 32, "__simple_riscv_zca_cbeqz_predecode_v1", "mir_cbeqz_predecode_intrinsic"),
    CoreConfig.rv32_zca_mission_critical())
val bnez = lower_strict_mir_function_to_hwir(
    hardware_cb_predecode_intrinsic_function(56, 64, "__simple_riscv_zca_cbnez_predecode_v1", "mir_cbnez_predecode_intrinsic"),
    CoreConfig.rv64_zca_mission_critical())
expect(beqz.is_success()).to_equal(true)
expect(bnez.is_success()).to_equal(true)
expect(beqz.uses_legacy_fallback()).to_equal(false)
expect(bnez.uses_legacy_fallback()).to_equal(false)
if val module = beqz.module:
    expect(module.origins[0].source_name).to_equal("zca.c.beqz")
    expect(module.port_width("rs1_value")).to_equal(32)
    expect(module.port_width("next_pc")).to_equal(32)
    expect(render_strict_hwir_vhdl(module).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
if val module = bnez.module:
    expect(module.origins[0].source_name).to_equal("zca.c.bnez")
    expect(module.port_width("rs1_value")).to_equal(64)
    expect(module.port_width("redirect_target")).to_equal(56)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject C.BEQZ predecode when its architectural operand is not Bits[XLEN]

- should reject C.BEQZ predecode when its architectural operand is not Bits[XLEN]
- Submit C.BEQZ predecode with an operand outside the configured architectural width
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-SIGNATURE: strict C.BEQZ predecode lowering requires Bits[16], Bit... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject C.BEQZ predecode when its architectural operand is not Bits[XLEN]")
step("Submit C.BEQZ predecode with an operand outside the configured architectural width")
var mir_function = hardware_cb_predecode_intrinsic_function(32, 32,
    "__simple_riscv_zca_cbeqz_predecode_v1", "mir_cbeqz_bad_operand")
mir_function.signature = MirSignature(params: [bits_type(16), bits_type(32), bits_type(5), bits_type(31)],
    return_type: cj_predecode_result_type(32), is_variadic: false)
val cb_rs1_local = mir_function.locals[3]
cb_rs1_local.type_ = bits_type(31)
mir_function.locals[3] = cb_rs1_local
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-SIGNATURE: strict C.BEQZ predecode lowering requires Bits[16], Bits[PA], Bits[5], Bits[XLEN] -> (Bits[32], Bits[2], Bool, Bits[PA], Bool, Bits[PA])")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should extract real-MIR C.ADD with elaborated RV32/RV64 hint behavior

- should extract real-MIR C.ADD with elaborated RV32/RV64 hint behavior
- Lower the C.ADD semantic fixture for its concrete RV32 and RV64 configurations
   - Expected: rv32.is_success() is true
   - Expected: rv64.is_success() is true
   - Expected: rv32.uses_legacy_fallback() is false
   - Expected: rv64.uses_legacy_fallback() is false
   - Expected: module32.origins[0].source_name equals `zca.c.add`
   - Expected: module32.summary.comb_op_count equals `18`
   - Expected: module32.select_ops[1].condition equals `rd_is_zero`
   - Expected: false is true
   - Expected: module64.summary.comb_op_count equals `16`
   - Expected: module64.signals.len() equals `15`
   - Expected: render_strict_hwir_vhdl(module64).is_success() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should extract real-MIR C.ADD with elaborated RV32/RV64 hint behavior")
step("Lower the C.ADD semantic fixture for its concrete RV32 and RV64 configurations")
val rv32 = lower_strict_mir_function_to_hwir(hardware_cadd_intrinsic_function(), CoreConfig.rv32_zca_mission_critical())
val rv64 = lower_strict_mir_function_to_hwir(hardware_cadd_intrinsic_function(), CoreConfig.rv64_zca_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv64.is_success()).to_equal(true)
expect(rv32.uses_legacy_fallback()).to_equal(false)
expect(rv64.uses_legacy_fallback()).to_equal(false)
if val module32 = rv32.module:
    expect(module32.origins[0].source_name).to_equal("zca.c.add")
    expect(module32.summary.comb_op_count).to_equal(18)
    expect(module32.select_ops[1].condition).to_equal("rd_is_zero")
else:
    expect(false).to_equal(true)
if val module64 = rv64.module:
    expect(module64.summary.comb_op_count).to_equal(16)
    expect(module64.signals.len()).to_equal(15)
    expect(render_strict_hwir_vhdl(module64).is_success()).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### should reject a terminal compressed graph outside the common-critical product profile

- should reject a terminal compressed graph outside the common-critical product profile
- Lower a terminal compressed graph under a non-admitted product profile
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-COMPRESSED-PROFILE: strict terminal decode requires the zca-common-cri... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a terminal compressed graph outside the common-critical product profile")
step("Lower a terminal compressed graph under a non-admitted product profile")
val result = lower_strict_mir_function_to_hwir(hardware_cebreak_decode_function(), CoreConfig.rv32())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-COMPRESSED-PROFILE: strict terminal decode requires the zca-common-critical product profile")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject an unapproved terminal parcel literal without legacy fallback

- should reject an unapproved terminal parcel literal without legacy fallback
- Lower an unapproved terminal parcel literal through the strict boundary
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-CONSTANT: strict terminal decode has no approved critical parcel l... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject an unapproved terminal parcel literal without legacy fallback")
step("Lower an unapproved terminal parcel literal through the strict boundary")
var mir_function = hardware_cebreak_decode_function()
mir_function = with_block_instruction(mir_function, 0, 0, MirInst(kind: MirInstKind.Const(LocalId(id: 1), MirConstValue.Int(2), u32_type()), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-CONSTANT: strict terminal decode has no approved critical parcel literal")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a malformed C.EBREAK branch edge without legacy fallback

- should reject a malformed C.EBREAK branch edge without legacy fallback
- Corrupt the C.EBREAK branch edge before strict semantic extraction
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-CFG: strict terminal miss branch must jump to the join block`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a malformed C.EBREAK branch edge without legacy fallback")
step("Corrupt the C.EBREAK branch edge before strict semantic extraction")
var mir_function = hardware_cebreak_decode_function()
mir_function = with_block_terminator(mir_function, 2, MirTerminator.Goto(BlockId(id: 1)))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-CFG: strict terminal miss branch must jump to the join block")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a non-hardware real MIR function without a legacy fallback

- should reject a non-hardware real MIR function without a legacy fallback
- Submit a real-MIR function lacking hardware metadata to strict lowering
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-NOT-HARDWARE: strict MIR lowering requires @hardware metadata`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a non-hardware real MIR function without a legacy fallback")
step("Submit a real-MIR function lacking hardware metadata to strict lowering")
var mir_function = hardware_and_function()
mir_function.has_vhdl_metadata = false
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-NOT-HARDWARE: strict MIR lowering requires @hardware metadata")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject an open or variadic MIR local boundary before semantic extraction

- should reject an open or variadic MIR local boundary before semantic extraction
- Submit open and variadic local boundaries before strict semantic extraction
   - Expected: variadic_result.is_success() is false
   - Expected: variadic_result.diagnostic equals `HWIR-E-MIR-SIGNATURE: strict MIR lowering requires a non-variadic signature`
   - Expected: variadic_result.uses_legacy_fallback() is false
   - Expected: wrong_arg_result.is_success() is false
   - Expected: wrong_arg_result.diagnostic equals `HWIR-E-MIR-LOCAL: strict MIR Arg locals must match the fixed signature`
   - Expected: wrong_arg_result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject an open or variadic MIR local boundary before semantic extraction")
step("Submit open and variadic local boundaries before strict semantic extraction")
var variadic = hardware_cli_intrinsic_function()
variadic.signature.is_variadic = true
val variadic_result = lower_strict_mir_function_to_hwir(variadic, CoreConfig.rv32_zca_mission_critical())
expect(variadic_result.is_success()).to_equal(false)
expect(variadic_result.diagnostic).to_equal("HWIR-E-MIR-SIGNATURE: strict MIR lowering requires a non-variadic signature")
expect(variadic_result.uses_legacy_fallback()).to_equal(false)

var wrong_arg_type = hardware_cli_intrinsic_function()
val wrong_arg_local = wrong_arg_type.locals[0]
wrong_arg_local.type_ = bool_type()
wrong_arg_type.locals[0] = wrong_arg_local
val wrong_arg_result = lower_strict_mir_function_to_hwir(wrong_arg_type, CoreConfig.rv32_zca_mission_critical())
expect(wrong_arg_result.is_success()).to_equal(false)
expect(wrong_arg_result.diagnostic).to_equal("HWIR-E-MIR-LOCAL: strict MIR Arg locals must match the fixed signature")
expect(wrong_arg_result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a duplicate real-MIR local ID before semantic extraction

- should reject a duplicate real-MIR local ID before semantic extraction
- Duplicate a real-MIR local identifier before strict semantic extraction
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-LOCAL: strict MIR local IDs must be unique`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a duplicate real-MIR local ID before semantic extraction")
step("Duplicate a real-MIR local identifier before strict semantic extraction")
var mir_function = hardware_cli_intrinsic_function()
mir_function.locals.push(MirLocal(id: LocalId(id: 0), name: Some("duplicate_parcel"), type_: u32_type(), kind: LocalKind.Temp))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-LOCAL: strict MIR local IDs must be unique")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject dangling and mistyped real-MIR values before semantic extraction

- should reject dangling and mistyped real-MIR values before semantic extraction
- Submit dangling and mistyped values before strict semantic extraction
   - Expected: dangling_result.is_success() is false
   - Expected: dangling_result.diagnostic equals `HWIR-E-MIR-LOCAL: intrinsic destination must resolve to a declared local`
   - Expected: dangling_result.uses_legacy_fallback() is false
   - Expected: bad_copy_result.is_success() is false
   - Expected: bad_copy_result.diagnostic equals `HWIR-E-MIR-LOCAL: copy values must resolve to equal declared types`
   - Expected: bad_copy_result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject dangling and mistyped real-MIR values before semantic extraction")
step("Submit dangling and mistyped values before strict semantic extraction")
var dangling = hardware_cli_intrinsic_function()
dangling = with_entry_instruction(dangling, MirInst(kind: MirInstKind.Intrinsic(Some(LocalId(id: 99)), "__simple_riscv_zca_cli_row_v1", [copy(0)]), span: nil))
val dangling_result = lower_strict_mir_function_to_hwir(dangling, CoreConfig.rv32_zca_mission_critical())
expect(dangling_result.is_success()).to_equal(false)
expect(dangling_result.diagnostic).to_equal("HWIR-E-MIR-LOCAL: intrinsic destination must resolve to a declared local")
expect(dangling_result.uses_legacy_fallback()).to_equal(false)

var bad_copy = hardware_cebreak_decode_function()
bad_copy = with_block_instruction(bad_copy, 1, 1, MirInst(kind: MirInstKind.Copy(LocalId(id: 5), LocalId(id: 2)), span: nil))
val bad_copy_result = lower_strict_mir_function_to_hwir(bad_copy, CoreConfig.rv32_zca_mission_critical())
expect(bad_copy_result.is_success()).to_equal(false)
expect(bad_copy_result.diagnostic).to_equal("HWIR-E-MIR-LOCAL: copy values must resolve to equal declared types")
expect(bad_copy_result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject malformed binary and branch types before semantic extraction

- should reject malformed binary and branch types before semantic extraction
- Submit malformed binary and branch operand types to strict lowering
   - Expected: bad_binary_result.is_success() is false
   - Expected: bad_binary_result.uses_legacy_fallback() is false
   - Expected: bad_condition_result.is_success() is false
   - Expected: bad_condition_result.uses_legacy_fallback() is false
   - Expected: bad_target_result.is_success() is false
   - Expected: bad_target_result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject malformed binary and branch types before semantic extraction")
step("Submit malformed binary and branch operand types to strict lowering")
var bad_binary = hardware_and_function()
val bad_binary_local = bad_binary.locals[2]
bad_binary_local.type_ = u32_type()
bad_binary.locals[2] = bad_binary_local
val bad_binary_result = lower_strict_mir_function_to_hwir(bad_binary, CoreConfig.rv32())
expect(bad_binary_result.is_success()).to_equal(false)
expect(bad_binary_result.diagnostic).to_equal(
    "HWIR-E-MIR-BINOP: strict MIR binary operands and result must preserve one exact type")
expect(bad_binary_result.uses_legacy_fallback()).to_equal(false)

var bad_condition = hardware_cebreak_decode_function()
val bad_condition_local = bad_condition.locals[2]
bad_condition_local.type_ = u32_type()
bad_condition.locals[2] = bad_condition_local
val bad_condition_result = lower_strict_mir_function_to_hwir(bad_condition,
    CoreConfig.rv32_zca_mission_critical())
expect(bad_condition_result.is_success()).to_equal(false)
expect(bad_condition_result.diagnostic).to_equal(
    "HWIR-E-MIR-BINOP: strict MIR comparison operands must match and produce Bool")
expect(bad_condition_result.uses_legacy_fallback()).to_equal(false)

var bad_target = hardware_cebreak_decode_function()
val bad_target_block = bad_target.blocks[0]
bad_target_block.terminator = MirTerminator.If(copy(2), BlockId(id: 1), BlockId(id: 99))
bad_target.blocks[0] = bad_target_block
val bad_target_result = lower_strict_mir_function_to_hwir(bad_target,
    CoreConfig.rv32_zca_mission_critical())
expect(bad_target_result.is_success()).to_equal(false)
expect(bad_target_result.diagnostic).to_equal(
    "HWIR-E-MIR-CFG: branch targets must resolve to declared blocks")
expect(bad_target_result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a terminal join with hidden instructions before semantic extraction

- should reject a terminal join with hidden instructions before semantic extraction
- Insert hidden work into a terminal join before strict semantic extraction
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-CFG: strict terminal join block must not contain instructions`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a terminal join with hidden instructions before semantic extraction")
step("Insert hidden work into a terminal join before strict semantic extraction")
var contaminated = hardware_cebreak_decode_function()
var blocks = contaminated.blocks
var join = blocks[3]
join.instructions = [MirInst(kind: MirInstKind.Const(LocalId(id: 4), MirConstValue.Int(0), u32_type()), span: nil)]
blocks[3] = join
contaminated.blocks = blocks
val result = lower_strict_mir_function_to_hwir(contaminated, CoreConfig.rv32_zca_mission_critical())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-CFG: strict terminal join block must not contain instructions")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

#### should reject a wrong real MIR operation before emission

- should reject a wrong real MIR operation before emission
- Replace the supported real-MIR operation before strict emission
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-INSTRUCTION: strict MIR lowering requires one supported bitwise in... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject a wrong real MIR operation before emission")
step("Replace the supported real-MIR operation before strict emission")
var mir_function = hardware_and_function()
mir_function = with_entry_instruction(mir_function, MirInst(kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.BitXor, copy(0), copy(1)), span: nil))
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-INSTRUCTION: strict MIR lowering requires one supported bitwise instruction")
```

</details>

#### should reject clocked MIR until sequential HWIR is implemented

- should reject clocked MIR until sequential HWIR is implemented
- Mark the real-MIR fixture clocked before strict HWIR extraction
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-CLOCKED: strict MIR lowering currently supports combinational function... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject clocked MIR until sequential HWIR is implemented")
step("Mark the real-MIR fixture clocked before strict HWIR extraction")
var mir_function = hardware_and_function()
mir_function.vhdl_metadata = hardware_metadata(true)
val result = lower_strict_mir_function_to_hwir(mir_function, CoreConfig.rv32())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-CLOCKED: strict MIR lowering currently supports combinational functions only")
```

</details>

#### should route a real single-function MIR module through strict HWIR only

- should route a real single-function MIR module through strict HWIR only
- Compile a single-function real-MIR module through the strict HWIR route
   - Expected: result.is_success() is true
   - Expected: result.route equals `hwir-strict`
   - Expected: result.config_xlen equals `32`
   - Expected: result.vhdl contains `entity mir_bool_and is`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should route a real single-function MIR module through strict HWIR only")
step("Compile a single-function real-MIR module through the strict HWIR route")
val result = compile_strict_hwir_module(strict_module(hardware_and_function()), CoreConfig.rv32())
expect(result.is_success()).to_equal(true)
expect(result.route).to_equal("hwir-strict")
expect(result.config_xlen).to_equal(32)
expect(result.vhdl.contains("entity mir_bool_and is")).to_equal(true)
```

</details>

#### should route the real parcel mask module through strict HWIR only

- should route the real parcel mask module through strict HWIR only
- Compile the real parcel-mask module through the strict HWIR route
   - Expected: result.is_success() is true
   - Expected: result.route equals `hwir-strict`
   - Expected: result.config_profile equals `rv32-zca`
   - Expected: result.vhdl contains `entity mir_u32_parcel_mask is`
   - Expected: result.vhdl contains `00000000000000001111111111111111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should route the real parcel mask module through strict HWIR only")
step("Compile the real parcel-mask module through the strict HWIR route")
val result = compile_strict_hwir_module(strict_module(hardware_u32_parcel_mask_function()), CoreConfig.rv32_zca_integer())
expect(result.is_success()).to_equal(true)
expect(result.route).to_equal("hwir-strict")
expect(result.config_profile).to_equal("rv32-zca")
expect(result.vhdl.contains("entity mir_u32_parcel_mask is")).to_equal(true)
expect(result.vhdl.contains("00000000000000001111111111111111")).to_equal(true)
```

</details>

#### should reject an unsupported real MIR module without a legacy route

- should reject an unsupported real MIR module without a legacy route
- Compile an unsupported real-MIR module and require no legacy route
   - Expected: result.is_success() is false
   - Expected: result.diagnostic equals `HWIR-E-MIR-INSTRUCTION: strict MIR lowering requires one supported bitwise in... (full value in folded executable source)`
   - Expected: result.uses_legacy_fallback() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject an unsupported real MIR module without a legacy route")
step("Compile an unsupported real-MIR module and require no legacy route")
var mir_function = hardware_and_function()
mir_function = with_entry_instruction(mir_function, MirInst(kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.BitXor, copy(0), copy(1)), span: nil))
val result = compile_strict_hwir_module(strict_module(mir_function), CoreConfig.rv32())
expect(result.is_success()).to_equal(false)
expect(result.diagnostic).to_equal("HWIR-E-MIR-INSTRUCTION: strict MIR lowering requires one supported bitwise instruction")
expect(result.uses_legacy_fallback()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strict HWIR real MIR extraction.
- strict HWIR real MIR extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f196ce83ec0d284560c760b4fc15d2bc3ff7aa9203cfbace646d36a9f4bed7a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f196ce83ec0d284560c760b4fc15d2bc3ff7aa9203cfbace646d36a9f4bed7a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f196ce83ec0d284560c760b4fc15d2bc3ff7aa9203cfbace646d36a9f4bed7a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 52 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:522:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract every closed RV64-only Zca row intrinsic without fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:522:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract every closed RV64-only Zca row intrinsic without fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:549:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every closed RV64-only Zca row intrinsic for RV32 elaboration' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:549:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject every closed RV64-only Zca row intrinsic for RV32 elaboration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:567:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed and prefix-lookalike RV64 Zca intrinsics at the closed boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:567:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed and prefix-lookalike RV64 Zca intrinsics at the closed boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:590:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract the real Bool BitAnd and its MIR origins' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:614:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract a fixed-width u32 BitAnd without using XLEN for datapath width' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl:632:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract a fixed-width u32 BitOr for instruction assembly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
