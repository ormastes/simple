# Vhdl Memory Templates Specification

> _Focused ROM/RAM inference-template coverage._

<!-- sdn-diagram:id=vhdl_memory_templates_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_memory_templates_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_memory_templates_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_memory_templates_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Memory Templates Specification

## Scenarios

### VHDL memory template renderer
_Focused ROM/RAM inference-template coverage._

#### renders a static ROM constant with explicit initializer values

1. data type: "std logic vector
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_static_rom_template(VhdlStaticRomTemplate(
    name: "coeff_rom",
    type_name: "coeff_rom_t",
    data_type: "std_logic_vector(7 downto 0)",
    depth: 4,
    values: ["x\"11\"", "x\"22\""],
    default_value: "x\"00\""
))

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl).to_contain("type coeff_rom_t is array (0 to 3) of std_logic_vector(7 downto 0);")
expect(vhdl).to_contain("constant coeff_rom : coeff_rom_t := (")
expect(vhdl).to_contain("0 => x\"11\",")
expect(vhdl).to_contain("1 => x\"22\",")
expect(vhdl).to_contain("others => x\"00\"")
```

</details>

#### renders a registered ROM read process

1. data type: "unsigned
2. values: ["to unsigned
3. default value: "to unsigned
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_registered_rom_read_template(VhdlRegisteredRomReadTemplate(
    name: "lookup_rom",
    type_name: "lookup_rom_t",
    data_type: "unsigned(15 downto 0)",
    depth: 8,
    values: ["to_unsigned(3, 16)", "to_unsigned(5, 16)"],
    default_value: "to_unsigned(0, 16)",
    clock: "clk",
    address: "addr",
    data_out: "q"
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
expect(artifact.declarations).to_contain("constant lookup_rom : lookup_rom_t := (")
expect(artifact.body).to_contain("lookup_rom_read: process(clk)")
expect(artifact.body).to_contain("if rising_edge(clk) then")
expect(artifact.body).to_contain("q <= lookup_rom(to_integer(unsigned(addr)));")
```

</details>

#### renders read-first single-port synchronous RAM policy

1. data type: "std logic vector
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.ReadFirst
))

expect(result.is_ok()).to_equal(true)
val artifact = result.unwrap()
expect(artifact.declarations).to_contain("signal sample_ram : sample_ram_t := (others => x\"00000000\");")
expect(artifact.body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
expect(artifact.body).to_contain("if we = '1' then")
expect(artifact.body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
```

</details>

#### renders write-first single-port synchronous RAM policy

1. data type: "std logic vector
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.WriteFirst
))

expect(result.is_ok()).to_equal(true)
val body = result.unwrap().body
expect(body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
expect(body).to_contain("dout <= din;")
expect(body).to_contain("else")
expect(body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
```

</details>

#### renders no-change single-port synchronous RAM policy

1. data type: "std logic vector
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.NoChange
))

expect(result.is_ok()).to_equal(true)
val body = result.unwrap().body
expect(body).to_contain("if we = '1' then")
expect(body).to_contain("sample_ram(to_integer(unsigned(addr))) <= din;")
expect(body).to_contain("else")
expect(body).to_contain("dout <= sample_ram(to_integer(unsigned(addr)));")
```

</details>

#### rejects ambiguous read-during-write policies with diagnostics

1. data type: "std logic vector
2. read during write: VhdlReadDuringWritePolicy Ambiguous
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-RDW-AMBIGUOUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_single_port_sync_ram_template(VhdlSinglePortSyncRamTemplate(
    name: "sample_ram",
    type_name: "sample_ram_t",
    data_type: "std_logic_vector(31 downto 0)",
    depth: 16,
    clock: "clk",
    write_enable: "we",
    address: "addr",
    write_data: "din",
    read_data: "dout",
    initial_value: "x\"00000000\"",
    read_during_write: VhdlReadDuringWritePolicy.Ambiguous("source did not choose old, new, or unchanged read data")
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-RDW-AMBIGUOUS")
expect(diagnostic.message).to_contain("Vendor-safe VHDL memory policy requires explicit read-during-write behavior")
```

</details>

#### renders a constrained signal memory with a named array type

1. data type: "unsigned
2. initial value: Some
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "line_buffer",
    type_name: "line_buffer_memory_t",
    data_type: "unsigned(7 downto 0)",
    depth: 64,
    initial_value: Some("to_unsigned(0, 8)")
))

expect(result.is_ok()).to_equal(true)
val vhdl = result.unwrap().vhdl
expect(vhdl).to_contain("type line_buffer_memory_t is array (0 to 63) of unsigned(7 downto 0);")
expect(vhdl).to_contain("signal line_buffer : line_buffer_memory_t := (others => to_unsigned(0, 8));")
```

</details>

#### rejects unconstrained signal memory before VHDL emission

1. data type: "std logic vector
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-UNCONSTRAINED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "dynamic_buffer",
    type_name: "dynamic_buffer_memory_t",
    data_type: "std_logic_vector(7 downto 0)",
    depth: 0,
    initial_value: nil
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-UNCONSTRAINED")
expect(diagnostic.message).to_contain("concrete positive depth before vendor-safe VHDL emission")
```

</details>

#### rejects nested general memory before anonymous array VHDL

1. data type: "array
   - Expected: result.is_err() is true
   - Expected: diagnostic.code equals `VHDL-MEM-GENERAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = render_constrained_signal_memory_template(VhdlConstrainedSignalMemoryTemplate(
    name: "matrix",
    type_name: "matrix_memory_t",
    data_type: "array (0 to 3) of unsigned(7 downto 0)",
    depth: 4,
    initial_value: nil
))

expect(result.is_err()).to_equal(true)
val diagnostic = result.unwrap_err()
expect(diagnostic.code).to_equal("VHDL-MEM-GENERAL")
expect(diagnostic.message).to_contain("nested or general array element type")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_memory_templates_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VHDL memory template renderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
