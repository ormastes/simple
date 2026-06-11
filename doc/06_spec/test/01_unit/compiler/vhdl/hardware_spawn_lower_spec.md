# hardware_spawn_lower_spec

> Hardware Spawn Lower Specification

<!-- sdn-diagram:id=hardware_spawn_lower_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hardware_spawn_lower_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hardware_spawn_lower_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hardware_spawn_lower_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hardware_spawn_lower_spec

Hardware Spawn Lower Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-hardware-spawn |
| Category | Backend |
| Difficulty | 3/5 |
| Status | Active |
| Source | `test/01_unit/compiler/vhdl/hardware_spawn_lower_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Hardware Spawn Lower Specification

Tests typed return labels, hardware call lowering, and bit-width semantics
for the VHDL hardware spawn pipeline.

## Scenarios

### HardwareAttr preservation

#### creates combinational hardware attr

1. var attr = HardwareAttr hardware
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("full_adder")
check(attr.is_hardware())
check(attr.is_clocked == false)
check(attr.is_generic == false)
check(attr.entity_name == "full_adder")
```

</details>

#### creates clocked hardware attr

1. var attr = HardwareAttr clocked
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.clocked("pc_reg")
check(attr.is_hardware())
check(attr.is_clocked == true)
```

</details>

#### creates generic hardware attr

1. var attr = HardwareAttr generic hw
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.generic_hw("param_adder")
check(attr.is_hardware())
check(attr.is_generic == true)
```

</details>

#### attaches two return labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. check
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
check(labeled.label_count == 2)
check(labeled.label_name_at(0) == "sum")
check(labeled.label_type_at(0) == "u1")
check(labeled.label_name_at(1) == "cout")
check(labeled.label_type_at(1) == "u1")
```

</details>

#### attaches three return labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with three labels
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("decode")
var labeled = attr.with_three_labels("opcode", "u7", "rd", "u5", "funct3", "u3")
check(labeled.label_count == 3)
check(labeled.label_name_at(2) == "funct3")
```

</details>

#### rejects duplicate labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("out", "u1", "out", "u1")
check(labeled.has_duplicate_label())
```

</details>

### LabelValidation

#### passes for unique labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var v = validate hardware attr
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var v = validate_hardware_attr(labeled)
check(v.is_valid)
```

</details>

#### fails for duplicate labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var v = validate hardware attr
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("x", "u1", "x", "u1")
var v = validate_hardware_attr(labeled)
check(not v.is_valid)
check(v.has_duplicates)
```

</details>

#### fails for same-type anonymous returns

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var v = validate hardware attr
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("anon")
var labeled = attr.with_labels("", "u1", "", "u1")
var v = validate_hardware_attr(labeled)
check(not v.is_valid)
check(v.has_anonymous)
```

</details>

### ReturnLabel

#### generates output port

1. var lbl = ReturnLabel output
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lbl = ReturnLabel.output("sum", "u1", 1, 0)
check(lbl.port_direction() == "out")
check(lbl.vhdl_type() == "std_logic")
```

</details>

#### generates wide output port

1. var lbl = ReturnLabel output
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lbl = ReturnLabel.output("result", "u32", 32, 0)
check(lbl.vhdl_type() == "std_logic_vector(31 downto 0)")
```

</details>

#### generates input port

1. var lbl = ReturnLabel input
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lbl = ReturnLabel.input("a", "u8", 8, 0)
check(lbl.port_direction() == "in")
check(lbl.vhdl_type() == "std_logic_vector(7 downto 0)")
```

</details>

### deterministic instance naming

#### generates inst0 for first call

1. var name = deterministic instance name
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var name = deterministic_instance_name("adder", 0)
check(name == "adder_inst0")
```

</details>

#### generates inst1 for second call

1. var name = deterministic instance name
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var name = deterministic_instance_name("adder", 1)
check(name == "adder_inst1")
```

</details>

### CallSite

#### allows direct calls

1. var site = CallSite direct
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var site = CallSite.direct("top", "adder", 0)
check(site.can_lower())
```

</details>

#### rejects indirect calls

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var site = CallSite direct
2. site = site with args
3. var attr = HardwareAttr hardware
4. var ctx = CallLowerContext create
5. var result = lower call site
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var attr = HardwareAttr hardware
2. var ctx = CallLowerContext create
3. var result = lower call site
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var attr = HardwareAttr hardware
2. var ctx = CallLowerContext create
3. var result = lower call site
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var inst = HardwareCallInstance create
2. inst = inst add port
3. inst = inst add port
4. inst = inst add port
5. var pm = inst vhdl port map
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inst = HardwareCallInstance.create("fa_inst0", "full_adder")
inst = inst.add_port("a", "sig_a")
inst = inst.add_port("b", "sig_b")
inst = inst.add_port("sum", "fa_inst0_sum")
var pm = inst.vhdl_port_map()
check(pm == "a => sig_a, b => sig_b, sum => fa_inst0_sum")
```

</details>

#### generates full VHDL instantiation

1. var inst = HardwareCallInstance create
2. inst = inst add port
3. inst = inst add port
4. var vhdl = inst vhdl instantiation
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inst = HardwareCallInstance.create("fa_inst0", "full_adder")
inst = inst.add_port("a", "sig_a")
inst = inst.add_port("b", "sig_b")
var vhdl = inst.vhdl_instantiation()
check(vhdl == "fa_inst0 : entity work.full_adder port map (a => sig_a, b => sig_b);")
```

</details>

### TempSignal allocation

#### allocates output temp signals

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var temps = allocate temp signals
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var temps = allocate_temp_signals(labeled, "adder_inst0")
check(temps.len() == 2)
```

</details>

### BitWidth types

#### generates std_logic for u1

1. var bw = BitWidth unsigned
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bw = BitWidth.unsigned(1)
check(bw.vhdl_type() == "std_logic")
check(bw.name == "u1")
```

</details>

#### generates unsigned for u32

1. var bw = BitWidth unsigned
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bw = BitWidth.unsigned(32)
check(bw.vhdl_type() == "unsigned(31 downto 0)")
```

</details>

#### generates signed for s32

1. var bw = BitWidth signed
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bw = BitWidth.signed(32)
check(bw.vhdl_type() == "signed(31 downto 0)")
```

</details>

#### checks width fitting

1. var bw = BitWidth unsigned
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bw = BitWidth.unsigned(12)
check(bw.fits_in(32))
check(not bw.fits_in(8))
```

</details>

#### returns rv32i standard widths

1. var widths = rv32i bitwidths
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var widths = rv32i_bitwidths()
check(widths.len() == 9)
```

</details>

### BitSlice extraction

#### extracts opcode field

1. var s = BitSlice opcode
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.opcode()
check(s.is_valid())
check(s.result_width == 7)
check(s.vhdl_expr("instr") == "instr(6 downto 0)")
```

</details>

#### extracts rd field

1. var s = BitSlice rd
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.rd()
check(s.result_width == 5)
check(s.vhdl_expr("instr") == "instr(11 downto 7)")
```

</details>

#### extracts funct3 field

1. var s = BitSlice funct3
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.funct3()
check(s.result_width == 3)
```

</details>

#### extracts rs1 field

1. var s = BitSlice rs1
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.rs1()
check(s.result_width == 5)
```

</details>

#### extracts rs2 field

1. var s = BitSlice rs2
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.rs2()
check(s.result_width == 5)
```

</details>

#### extracts funct7 field

1. var s = BitSlice funct7
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = BitSlice.funct7()
check(s.result_width == 7)
```

</details>

#### validates slice bounds

1. var bad = BitSlice
2. check
3. var diag = validate bit slice
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad = BitSlice(source_width: 8, high_bit: 10, low_bit: 0, result_width: 11)
check(not bad.is_valid())
var diag = validate_bit_slice(bad)
check(diag.is_error)
check(diag.is_out_of_range())
```

</details>

### BitConcat

#### concatenates two signals

1. var cat = BitConcat create
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cat = BitConcat.create("high", 4, "low", 4)
check(cat.result_width == 8)
check(cat.is_valid())
check(cat.vhdl_expr() == "high & low")
```

</details>

### BitExtension

#### zero extends

1. var ext = BitExtension zero extend
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ext = BitExtension.zero_extend("sig12", 12, 32)
check(ext.is_extension())
check(not ext.is_truncation())
```

</details>

#### sign extends

1. var ext = BitExtension sign extend
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ext = BitExtension.sign_extend("imm12", 12, 32)
check(ext.is_extension())
check(ext.is_sign_extend)
```

</details>

#### truncates

1. var trunc = BitExtension truncate
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var trunc = BitExtension.truncate("wide", 32, 8)
check(trunc.is_truncation())
check(trunc.vhdl_expr() == "wide(7 downto 0)")
```

</details>

#### identity for same width

1. var id = BitExtension zero extend
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var id = BitExtension.zero_extend("x", 16, 16)
check(id.is_identity())
check(id.vhdl_expr() == "x")
```

</details>

### BitShift

#### generates shift left

1. var sh = BitShift sll
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = BitShift.sll("data", 32, 2)
check(sh.result_width() == 32)
check(sh.vhdl_expr() == "shift_left(data, 2)")
```

</details>

#### generates shift right logical

1. var sh = BitShift srl
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = BitShift.srl("data", 32, 5)
check(sh.vhdl_expr() == "shift_right(data, 5)")
```

</details>

### BitMask

#### generates AND mask

1. var m = BitMask mask and
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = BitMask.mask_and("opcode", 7, "\"1111111\"")
check(m.vhdl_expr() == "opcode and \"1111111\"")
```

</details>

#### generates equality comparison

1. var m = BitMask compare eq
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = BitMask.compare_eq("opcode", 7, "\"0110011\"")
check(m.vhdl_expr() == "opcode = \"0110011\"")
```

</details>

### InstructionFormat

#### classifies R-type

1. var fmt = InstructionFormat r type
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fmt = InstructionFormat.r_type()
check(fmt.is_r_type())
check(not fmt.has_immediate())
```

</details>

#### classifies I-type

1. var fmt = InstructionFormat i type
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fmt = InstructionFormat.i_type()
check(fmt.is_i_type())
check(fmt.has_immediate())
check(fmt.imm_width == 12)
```

</details>

#### classifies B-type

1. var fmt = InstructionFormat b type
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fmt = InstructionFormat.b_type()
check(fmt.is_branch())
check(fmt.imm_width == 13)
```

</details>

### lower_hardware_spawn pipeline

#### lowers single call with labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var input = SpawnLowerInput single call
4. var output = lower hardware spawn
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var input = SpawnLowerInput.single_call("test", "add2", labeled, "add2", "full_adder", "sig_a", "sig_b")
var output = lower_hardware_spawn(input)
check(output.success)
check(output.instance_count == 1)
```

</details>

#### lowers two calls

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var input = SpawnLowerInput two calls
4. var output = lower hardware spawn
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("full_adder")
var labeled = attr.with_labels("sum", "u1", "cout", "u1")
var input = SpawnLowerInput.two_calls("test", "add2", labeled, "add2", "full_adder", "a0", "b0", "add2", "full_adder", "a1", "b1")
var output = lower_hardware_spawn(input)
check(output.success)
check(output.instance_count == 2)
```

</details>

#### rejects duplicate labels

1. var attr = HardwareAttr hardware
2. var labeled = attr with labels
3. var input = SpawnLowerInput single call
4. var output = lower hardware spawn
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var attr = HardwareAttr.hardware("bad")
var labeled = attr.with_labels("x", "u1", "x", "u1")
var input = SpawnLowerInput.single_call("test", "fn1", labeled, "fn1", "bad", "a", "b")
var output = lower_hardware_spawn(input)
check(output.has_errors())
```

</details>

#### handles empty call list

1. var attr = HardwareAttr hardware
2. var output = lower hardware spawn
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
