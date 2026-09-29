# Hardware Spawn Lower Specification

> Tests covering HardwareAttr preservation, LabelValidation, ReturnLabel, deterministic instance naming, CallSite, lower_call_site, HardwareCallInstance port map, TempSignal allocation, BitWidth types, BitSlice extraction, BitConcat, BitExtension, BitShift, BitMask, InstructionFormat, lower_hardware_spawn pipeline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardware Spawn Lower Specification

## Scenarios

### HardwareAttr preservation

#### creates combinational hardware attr

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates combinational hardware attr


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates combinational hardware attr")
var attr = HardwareAttr.hardware("full_adder")
check(attr.is_hardware())
check(attr.is_clocked == false)
check(attr.is_generic == false)
check(attr.entity_name == "full_adder")
```

</details>

#### creates clocked hardware attr

- creates clocked hardware attr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates clocked hardware attr")
var attr = HardwareAttr.clocked("pc_reg")
check(attr.is_hardware())
check(attr.is_clocked == true)
```

</details>

#### creates generic hardware attr

- creates generic hardware attr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates generic hardware attr")
var attr = HardwareAttr.generic_hw("param_adder")
check(attr.is_hardware())
check(attr.is_generic == true)
```

</details>

#### attaches two return labels

- attaches two return labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attaches two return labels")
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
check(labeled.has_labels())
check(labeled.label_count == 2)
check(labeled.label_name_at(0) == "sum")
check(labeled.label_type_at(0) == "u1")
check(labeled.label_name_at(1) == "cout")
check(labeled.label_type_at(1) == "u1")
```

</details>

#### attaches three return labels

- attaches three return labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attaches three return labels")
var attr = HardwareAttr.hardware("decode")
var labeled = attr.with_three_labels("opcode", "u7", "rd", "u5", "funct3", "u3")
check(labeled.label_count == 3)
check(labeled.label_name_at(2) == "funct3")
```

</details>

#### rejects duplicate labels

- rejects duplicate labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate labels")
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("out", "u1", "out", "u1")
check(labeled.has_duplicate_label())
```

</details>

### LabelValidation

#### passes for unique labels

- passes for unique labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes for unique labels")
var attr = HardwareAttr.hardware("adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var v = validate_hardware_attr(labeled)
check(v.is_valid)
```

</details>

#### fails for duplicate labels

- fails for duplicate labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for duplicate labels")
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("x", "u1", "x", "u1")
var v = validate_hardware_attr(labeled)
check(not v.is_valid)
check(v.has_duplicates)
```

</details>

#### fails for same-type anonymous returns

- fails for same-type anonymous returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails for same-type anonymous returns")
var attr = HardwareAttr.hardware("anon")
var labeled = attr.with_labels("", "u1", "", "u1")
var v = validate_hardware_attr(labeled)
check(not v.is_valid)
check(v.has_anonymous)
```

</details>

### ReturnLabel

#### generates output port

- generates output port


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates output port")
var lbl = ReturnLabel.output("sum", "u1", 1, 0)
check(lbl.port_direction() == "out")
check(lbl.vhdl_type() == "std_logic")
```

</details>

#### generates wide output port

- generates wide output port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates wide output port")
var lbl = ReturnLabel.output("result", "u32", 32, 0)
check(lbl.vhdl_type() == "std_logic_vector(31 downto 0)")
```

</details>

#### generates input port

- generates input port


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates input port")
var lbl = ReturnLabel.input("a", "u8", 8, 0)
check(lbl.port_direction() == "in")
check(lbl.vhdl_type() == "std_logic_vector(7 downto 0)")
```

</details>

### deterministic instance naming

#### generates inst0 for first call

- generates inst0 for first call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inst0 for first call")
var name = deterministic_instance_name("adder", 0)
check(name == "adder_inst0")
```

</details>

#### generates inst1 for second call

- generates inst1 for second call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inst1 for second call")
var name = deterministic_instance_name("adder", 1)
check(name == "adder_inst1")
```

</details>

### CallSite

#### allows direct calls

- allows direct calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows direct calls")
var site = CallSite.direct("top", "adder", 0)
check(site.can_lower())
```

</details>

#### rejects indirect calls

- rejects indirect calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects indirect calls")
var site = CallSite(
    caller_name: "top",
    callee_name: "unknown",
    call_index: 0,
    is_indirect: true,
    is_recursive: false,
    arg_count: 0,
    a0_name: "",
    a1_name: "",
    a2_name: ""
)
check(not site.can_lower())
```

</details>

### lower_call_site

#### lowers direct hardware call

- lowers direct hardware call


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers direct hardware call")
var site = CallSite.direct("top", "full_adder", 0)
site = site.with_args("sig_a", "sig_b")
var attr = HardwareAttr.hardware("full_adder")
var ctx = CallLowerContext.create("test_mod")
var result = lower_call_site(site, attr, ctx)
check(result.success)
check(result.instance_name == "full_adder_inst0")
```

</details>

#### rejects indirect call

- rejects indirect call


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects indirect call")
var site = CallSite(
    caller_name: "top",
    callee_name: "ptr",
    call_index: 0,
    is_indirect: true,
    is_recursive: false,
    arg_count: 0,
    a0_name: "",
    a1_name: "",
    a2_name: ""
)
var attr = HardwareAttr.hardware("ptr")
var ctx = CallLowerContext.create("test_mod")
var result = lower_call_site(site, attr, ctx)
check(result.is_rejected())
check(result.is_indirect)
```

</details>

#### rejects recursive call

- rejects recursive call


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects recursive call")
var site = CallSite(
    caller_name: "top",
    callee_name: "self_ref",
    call_index: 0,
    is_indirect: false,
    is_recursive: true,
    arg_count: 0,
    a0_name: "",
    a1_name: "",
    a2_name: ""
)
var attr = HardwareAttr.hardware("self_ref")
var ctx = CallLowerContext.create("test_mod")
var result = lower_call_site(site, attr, ctx)
check(result.is_rejected())
check(result.is_recursive)
```

</details>

### HardwareCallInstance port map

#### generates VHDL port map text

- generates VHDL port map text


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates VHDL port map text")
var inst = HardwareCallInstance.create("fa_inst0", "full_adder")
inst = inst.add_port("a", "sig_a")
inst = inst.add_port("b", "sig_b")
inst = inst.add_port("sum", "fa_inst0_sum")
check(inst.has_port("a"))
check(not inst.has_port("missing"))
check(inst.is_valid())
var pm = inst.vhdl_port_map()
check(pm == "a => sig_a, b => sig_b, sum => fa_inst0_sum")
```

</details>

#### generates full VHDL instantiation

- generates full VHDL instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates full VHDL instantiation")
var inst = HardwareCallInstance.create("fa_inst0", "full_adder")
inst = inst.add_port("a", "sig_a")
inst = inst.add_port("b", "sig_b")
var vhdl = inst.vhdl_instantiation()
check(vhdl == "fa_inst0 : entity work.full_adder port map (a => sig_a, b => sig_b);")
```

</details>

### TempSignal allocation

#### classifies port directions and lowering diagnostics

- classifies port directions and lowering diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies port directions and lowering diagnostics")
val input = PortMapEntry.input_port("a", "sig_a", 1)
val output = PortMapEntry.output_port("sum", "sig_sum", 1)
check(input.is_input())
check(not input.is_output())
check(output.is_output())
check(not output.is_input())
val clean = CallLowerContext.create("test_mod")
check(not clean.has_errors())
check(clean.with_error("bad port").has_errors())
```

</details>

#### allocates output temp signals

- allocates output temp signals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates output temp signals")
var attr = HardwareAttr.hardware("adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var temps = allocate_temp_signals(labeled, "adder_inst0")
check(temps.len() == 2)
```

</details>

### BitWidth types

#### generates std_logic for u1

- generates std_logic for u1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates std_logic for u1")
var bw = BitWidth.unsigned(1)
check(bw.vhdl_type() == "std_logic")
check(bw.name == "u1")
```

</details>

#### generates unsigned for u32

- generates unsigned for u32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates unsigned for u32")
var bw = BitWidth.unsigned(32)
check(bw.vhdl_type() == "unsigned(31 downto 0)")
```

</details>

#### generates signed for s32

- generates signed for s32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates signed for s32")
var bw = BitWidth.signed(32)
check(bw.vhdl_type() == "signed(31 downto 0)")
```

</details>

#### checks width fitting

- checks width fitting


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks width fitting")
var bw = BitWidth.unsigned(12)
check(bw.fits_in(32))
check(not bw.fits_in(8))
```

</details>

#### returns rv32i standard widths

- returns rv32i standard widths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns rv32i standard widths")
var widths = rv32i_bitwidths()
check(widths.len() == 9)
```

</details>

### BitSlice extraction

#### extracts opcode field

- extracts opcode field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts opcode field")
var s = BitSlice.opcode()
check(s.is_valid())
check(s.result_width == 7)
check(s.vhdl_expr("instr") == "instr(6 downto 0)")
```

</details>

#### extracts rd field

- extracts rd field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts rd field")
var s = BitSlice.rd()
check(s.result_width == 5)
check(s.vhdl_expr("instr") == "instr(11 downto 7)")
```

</details>

#### extracts funct3 field

- extracts funct3 field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts funct3 field")
var s = BitSlice.funct3()
check(s.result_width == 3)
```

</details>

#### extracts rs1 field

- extracts rs1 field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts rs1 field")
var s = BitSlice.rs1()
check(s.result_width == 5)
```

</details>

#### extracts rs2 field

- extracts rs2 field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts rs2 field")
var s = BitSlice.rs2()
check(s.result_width == 5)
```

</details>

#### extracts funct7 field

- extracts funct7 field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts funct7 field")
var s = BitSlice.funct7()
check(s.result_width == 7)
```

</details>

#### validates slice bounds

- validates slice bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates slice bounds")
var bad = BitSlice(source_width: 8, high_bit: 10, low_bit: 0, result_width: 11)
check(not bad.is_valid())
var diag = validate_bit_slice(bad)
check(diag.is_error)
check(diag.is_out_of_range())
```

</details>

### BitConcat

#### concatenates two signals

- concatenates two signals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates two signals")
var cat = BitConcat.create("high", 4, "low", 4)
check(cat.result_width == 8)
check(cat.is_valid())
check(cat.vhdl_expr() == "high & low")
```

</details>

### BitExtension

#### zero extends

- zero extends


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero extends")
var ext = BitExtension.zero_extend("sig12", 12, 32)
check(ext.is_extension())
check(not ext.is_truncation())
```

</details>

#### sign extends

- sign extends


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sign extends")
var ext = BitExtension.sign_extend("imm12", 12, 32)
check(ext.is_extension())
check(ext.is_sign_extend)
```

</details>

#### truncates

- truncates


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates")
var trunc = BitExtension.truncate("wide", 32, 8)
check(trunc.is_truncation())
check(trunc.vhdl_expr() == "wide(7 downto 0)")
```

</details>

#### identity for same width

- identity for same width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identity for same width")
var id = BitExtension.zero_extend("x", 16, 16)
check(id.is_identity())
check(id.vhdl_expr() == "x")
```

</details>

### BitShift

#### generates shift left

- generates shift left


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates shift left")
var sh = BitShift.sll("data", 32, 2)
check(sh.result_width() == 32)
check(sh.vhdl_expr() == "shift_left(data, 2)")
```

</details>

#### generates shift right logical

- generates shift right logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates shift right logical")
var sh = BitShift.srl("data", 32, 5)
check(sh.vhdl_expr() == "shift_right(data, 5)")
```

</details>

### BitMask

#### generates AND mask

- generates AND mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates AND mask")
var m = BitMask.mask_and("opcode", 7, "\"1111111\"")
check(m.vhdl_expr() == "opcode and \"1111111\"")
```

</details>

#### generates equality comparison

- generates equality comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates equality comparison")
var m = BitMask.compare_eq("opcode", 7, "\"0110011\"")
check(m.vhdl_expr() == "opcode = \"0110011\"")
```

</details>

### InstructionFormat

#### classifies R-type

- classifies R-type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies R-type")
var fmt = InstructionFormat.r_type()
check(fmt.is_r_type())
check(not fmt.has_immediate())
```

</details>

#### classifies I-type

- classifies I-type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies I-type")
var fmt = InstructionFormat.i_type()
check(fmt.is_i_type())
check(fmt.has_immediate())
check(fmt.imm_width == 12)
```

</details>

#### classifies B-type

- classifies B-type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies B-type")
var fmt = InstructionFormat.b_type()
check(fmt.is_branch())
check(fmt.imm_width == 13)
```

</details>

### lower_hardware_spawn pipeline

#### lowers single call with labels

- lowers single call with labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers single call with labels")
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var input = SpawnLowerInput.single_call("test", "add2", labeled, "add2", "full_adder", "sig_a", "sig_b")
var output = lower_hardware_spawn(input)
check(output.success)
check(output.instance_count == 1)
```

</details>

#### lowers two calls

- lowers two calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers two calls")
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var input = SpawnLowerInput.two_calls("test", "add2", labeled, "add2", "full_adder", "a0", "b0", "add2", "full_adder", "a1", "b1")
var output = lower_hardware_spawn(input)
check(output.success)
check(output.instance_count == 2)
```

</details>

#### rejects duplicate labels

- rejects duplicate labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate labels")
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("x", "u1", "x", "u1")
var input = SpawnLowerInput.single_call("test", "fn1", labeled, "fn1", "bad", "a", "b")
var output = lower_hardware_spawn(input)
check(output.has_errors())
```

</details>

#### handles empty call list

- handles empty call list


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty call list")
var attr = HardwareAttr.hardware("unused")
var input = SpawnLowerInput(
    module_name: "test",
    function_name: "none",
    attr: attr,
    call_count: 0,
    s0_caller: "",
    s0_callee: "",
    s0_arg0: "",
    s0_arg1: "",
    s1_caller: "",
    s1_callee: "",
    s1_arg0: "",
    s1_arg1: ""
)
var output = lower_hardware_spawn(input)
check(output.success)
check(output.instance_count == 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HardwareAttr preservation, LabelValidation, ReturnLabel, deterministic instance naming, CallSite, lower_call_site, HardwareCallInstance port map, TempSignal allocation, BitWidth types, BitSlice extraction, BitConcat, BitExtension, BitShift, BitMask, InstructionFormat, lower_hardware_spawn pipeline.
- HardwareAttr preservation
- LabelValidation
- ReturnLabel
- deterministic instance naming
- CallSite
- lower_call_site
- HardwareCallInstance port map
- TempSignal allocation
- BitWidth types
- BitSlice extraction
- BitConcat
- BitExtension
- BitShift
- BitMask
- InstructionFormat
- lower_hardware_spawn pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a612ac8a6b8c53280384286c5cdd8d75967b7d8d10700c99e965aaf5c56a0482`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a612ac8a6b8c53280384286c5cdd8d75967b7d8d10700c99e965aaf5c56a0482`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a612ac8a6b8c53280384286c5cdd8d75967b7d8d10700c99e965aaf5c56a0482`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl
mirror: doc/06_spec/01_unit/compiler/vhdl/hardware_spawn_lower_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/vhdl/hardware_spawn_lower_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/vhdl/hardware_spawn_lower_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates combinational hardware attr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates clocked hardware attr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates generic hardware attr' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
