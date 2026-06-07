# vhdl_abi_spec

> VHDL ABI Specification

<!-- sdn-diagram:id=vhdl_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_abi_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vhdl_abi_spec

VHDL ABI Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-abi |
| Category | Backend |
| Difficulty | 2/5 |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

VHDL ABI Specification

Tests for type-to-signal mapping, port ABI, and data width resolution.

## Scenarios

### VHDL ABI - data width resolution

#### returns 32 for i32

1. check
   - Expected: w.unwrap() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_i32())
check(w.?)
expect(w.unwrap()).to_equal(32)
```

</details>

#### returns 64 for i64

1. check
   - Expected: w.unwrap() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_i64())
check(w.?)
expect(w.unwrap()).to_equal(64)
```

</details>

#### returns 8 for u8

1. check
   - Expected: w.unwrap() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_u8())
check(w.?)
expect(w.unwrap()).to_equal(8)
```

</details>

#### returns 1 for bool

1. check
   - Expected: w.unwrap() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_bool())
check(w.?)
expect(w.unwrap()).to_equal(1)
```

</details>

#### returns custom width for Bits

1. check
   - Expected: w.unwrap() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_bits(12))
check(w.?)
expect(w.unwrap()).to_equal(12)
```

</details>

#### returns nil for f32

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_f32())
check(not w.?)
```

</details>

#### returns nil for Unit

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = vhdl_data_width_bits(make_unit())
check(not w.?)
```

</details>

#### returns element * size for arrays

1. check
   - Expected: w.unwrap() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = MirType(kind: MirTypeKind.Array(make_u8(), 4))
val w = vhdl_data_width_bits(arr)
check(w.?)
expect(w.unwrap()).to_equal(32)
```

</details>

### VHDL ABI - signal type mapping

#### maps i32 to signed(31 downto 0)

1. check
   - Expected: result.unwrap() equals `signed(31 downto 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_i32(), mapper)
check(result.?)
expect(result.unwrap()).to_equal("signed(31 downto 0)")
```

</details>

#### maps u32 to unsigned(31 downto 0)

1. check
   - Expected: result.unwrap() equals `unsigned(31 downto 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_u32(), mapper)
check(result.?)
expect(result.unwrap()).to_equal("unsigned(31 downto 0)")
```

</details>

#### maps bool to bit with unresolved mapper

1. check
   - Expected: result.unwrap() equals `bit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_bool(), mapper)
check(result.?)
expect(result.unwrap()).to_equal("bit")
```

</details>

#### maps bool to std_logic with resolved mapper

1. check
   - Expected: result.unwrap() equals `std_logic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create_resolved()
val result = vhdl_signal_type_for(make_bool(), mapper)
check(result.?)
expect(result.unwrap()).to_equal("std_logic")
```

</details>

#### maps unsigned Bits to unsigned

1. check
   - Expected: result.unwrap() equals `unsigned(15 downto 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_bits(16), mapper)
check(result.?)
expect(result.unwrap()).to_equal("unsigned(15 downto 0)")
```

</details>

#### maps signed Bits to signed

1. check
   - Expected: result.unwrap() equals `signed(7 downto 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_sbits(8), mapper)
check(result.?)
expect(result.unwrap()).to_equal("signed(7 downto 0)")
```

</details>

#### returns nil for f32

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for(make_f32(), mapper)
check(not result.?)
```

</details>

#### returns error comment for unsynthesizable via or_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val result = vhdl_signal_type_for_or_error(make_f32(), mapper, "test port")
expect(result).to_contain("ERROR")
expect(result).to_contain("unsynthesizable")
```

</details>

### VHDL ABI - port name sanitization

#### passes through simple names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("clk")).to_equal("clk")
```

</details>

#### replaces hyphens with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("data-in")).to_equal("data_in")
```

</details>

#### replaces dots with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("bus.addr")).to_equal("bus_addr")
```

</details>

#### collapses consecutive underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("a--b")).to_equal("a_b")
```

</details>

#### strips leading and trailing underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("-name-")).to_equal("name")
```

</details>

#### returns port for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("")).to_equal("port")
```

</details>

#### returns port for whitespace-only input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_abi_sanitize_port_name("   ")).to_equal("port")
```

</details>

### VHDL ABI - return ABI resolution

#### produces empty fields for Unit return

1. check
   - Expected: abi.fields.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_simple_func("void_fn", [], make_unit(), [])
val mapper = VhdlTypeMapper.create()
val abi = vhdl_resolve_return_abi(func, mapper)
check(not abi.is_tuple)
expect(abi.fields.len()).to_equal(0)
```

</details>

#### produces result_out for scalar i32 return

1. check
   - Expected: abi.fields.len() equals `1`
   - Expected: abi.fields[0].name equals `result_out`
   - Expected: abi.fields[0].type_name equals `signed(31 downto 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_local = make_return_local(0, make_i32())
val func = make_simple_func("scalar_fn", [], make_i32(), [ret_local])
val mapper = VhdlTypeMapper.create()
val abi = vhdl_resolve_return_abi(func, mapper)
check(not abi.is_tuple)
expect(abi.fields.len()).to_equal(1)
expect(abi.fields[0].name).to_equal("result_out")
expect(abi.fields[0].type_name).to_equal("signed(31 downto 0)")
```

</details>

#### produces numbered ports for anonymous tuple

1. check
   - Expected: abi.fields.len() equals `2`
   - Expected: abi.fields[0].name equals `out_0`
   - Expected: abi.fields[0].type_name equals `signed(31 downto 0)`
   - Expected: abi.fields[1].name equals `out_1`
   - Expected: abi.fields[1].type_name equals `bit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_ty = make_tuple([make_i32(), make_bool()])
val func = make_simple_func("tuple_fn", [], ret_ty, [])
val mapper = VhdlTypeMapper.create()
val abi = vhdl_resolve_return_abi(func, mapper)
check(abi.is_tuple)
expect(abi.fields.len()).to_equal(2)
expect(abi.fields[0].name).to_equal("out_0")
expect(abi.fields[0].type_name).to_equal("signed(31 downto 0)")
expect(abi.fields[1].name).to_equal("out_1")
expect(abi.fields[1].type_name).to_equal("bit")
```

</details>

#### uses labeled names for tuple with return field metadata

1. var meta = vhdl hardware metadata default
2. VhdlReturnFieldMetadata
3. VhdlReturnFieldMetadata
4. var func = make simple func
5. check
   - Expected: abi.fields.len() equals `2`
   - Expected: abi.fields[0].name equals `sum`
   - Expected: abi.fields[1].name equals `carry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_ty = make_tuple([make_i32(), make_bool()])
var meta = vhdl_hardware_metadata_default()
meta.is_hardware = true
meta.return_fields = [
    VhdlReturnFieldMetadata(label: "sum", type_text: "signed(31 downto 0)"),
    VhdlReturnFieldMetadata(label: "carry", type_text: "bit")
]
var func = make_simple_func("labeled_fn", [], ret_ty, [])
func.has_vhdl_metadata = true
func.vhdl_metadata = meta
val mapper = VhdlTypeMapper.create()
val abi = vhdl_resolve_return_abi(func, mapper)
check(abi.is_tuple)
expect(abi.fields.len()).to_equal(2)
expect(abi.fields[0].name).to_equal("sum")
expect(abi.fields[1].name).to_equal("carry")
```

</details>

### VHDL ABI - input port resolution

#### resolves named input ports from locals

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a_local = make_arg_local(1, 0, "a", make_i32())
val b_local = make_arg_local(2, 1, "b", make_i32())
val func = make_simple_func("adder", [make_i32(), make_i32()], make_i32(), [a_local, b_local])
val mapper = VhdlTypeMapper.create()
val ports = vhdl_resolve_input_ports(func, mapper)
expect(ports.len()).to_equal(2)
expect(ports[0].name).to_equal("a")
expect(ports[0].direction).to_equal("in")
expect(ports[0].type_name).to_equal("signed(31 downto 0)")
expect(ports[1].name).to_equal("b")
expect(ports[1].direction).to_equal("in")
```

</details>

#### falls back to argN for unnamed params

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_simple_func("anon", [make_u8()], make_unit(), [])
val mapper = VhdlTypeMapper.create()
val ports = vhdl_resolve_input_ports(func, mapper)
expect(ports.len()).to_equal(1)
expect(ports[0].name).to_equal("arg0")
expect(ports[0].type_name).to_equal("unsigned(7 downto 0)")
```

</details>

### VHDL ABI - full port list

#### combines input and output ports

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a_local = make_arg_local(1, 0, "data_in", make_i32())
val ret_local = make_return_local(2, make_i32())
val func = make_simple_func("passthrough", [make_i32()], make_i32(), [a_local, ret_local])
val mapper = VhdlTypeMapper.create()
val ports = vhdl_resolve_all_ports(func, mapper)
expect(ports.len()).to_equal(2)
expect(ports[0].name).to_equal("data_in")
expect(ports[0].direction).to_equal("in")
expect(ports[1].name).to_equal("result_out")
expect(ports[1].direction).to_equal("out")
```

</details>

### VHDL ABI - port collision detection

#### returns empty for no collisions

1. VhdlAbiPort
2. VhdlAbiPort
3. VhdlAbiPort
   - Expected: diags.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ports = [
    VhdlAbiPort(name: "a", direction: "in", type_name: "signed(31 downto 0)"),
    VhdlAbiPort(name: "b", direction: "in", type_name: "signed(31 downto 0)"),
    VhdlAbiPort(name: "result_out", direction: "out", type_name: "signed(31 downto 0)")
]
val diags = vhdl_abi_check_port_collisions(ports)
expect(diags.len()).to_equal(0)
```

</details>

#### detects duplicate port names

1. VhdlAbiPort
2. VhdlAbiPort
   - Expected: diags.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ports = [
    VhdlAbiPort(name: "data", direction: "in", type_name: "signed(31 downto 0)"),
    VhdlAbiPort(name: "data", direction: "out", type_name: "signed(31 downto 0)")
]
val diags = vhdl_abi_check_port_collisions(ports)
expect(diags.len()).to_equal(1)
expect(diags[0]).to_contain("Duplicate")
expect(diags[0]).to_contain("data")
```

</details>

### VHDL ABI - output validation

#### accepts Unit return

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_simple_func("void_fn", [], make_unit(), [])
val diags = vhdl_abi_validate_output(func)
expect(diags.len()).to_equal(0)
```

</details>

#### accepts scalar i32 return

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_simple_func("scalar_fn", [], make_i32(), [])
val diags = vhdl_abi_validate_output(func)
expect(diags.len()).to_equal(0)
```

</details>

#### rejects f32 return

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func = make_simple_func("float_fn", [], make_f32(), [])
val diags = vhdl_abi_validate_output(func)
expect(diags.len()).to_equal(1)
expect(diags[0]).to_contain("f32")
expect(diags[0]).to_contain("not directly synthesizable")
```

</details>

#### warns on tuple without metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_ty = make_tuple([make_i32(), make_bool()])
val func = make_simple_func("tuple_fn", [], ret_ty, [])
val diags = vhdl_abi_validate_output(func)
expect(diags.len()).to_equal(1)
expect(diags[0]).to_contain("no VHDL metadata")
```

</details>

#### warns on label count mismatch

1. var meta = vhdl hardware metadata default
2. VhdlReturnFieldMetadata
3. var func = make simple func
   - Expected: diags.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_ty = make_tuple([make_i32(), make_bool()])
var meta = vhdl_hardware_metadata_default()
meta.is_hardware = true
meta.return_fields = [
    VhdlReturnFieldMetadata(label: "sum", type_text: "signed(31 downto 0)")
]
var func = make_simple_func("mismatch_fn", [], ret_ty, [])
func.has_vhdl_metadata = true
func.vhdl_metadata = meta
val diags = vhdl_abi_validate_output(func)
expect(diags.len()).to_equal(1)
expect(diags[0]).to_contain("2-element tuple")
expect(diags[0]).to_contain("1 labeled return fields")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
