# VHDL Backend System Specification

> End-to-end system tests covering the complete VHDL backend workflow. Tests the full pipeline from type mapper through builder to output validation, plus constraint checker integration.

<!-- sdn-diagram:id=vhdl_backend_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_backend_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_backend_system_spec -> compiler
vhdl_backend_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_backend_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VHDL Backend System Specification

End-to-end system tests covering the complete VHDL backend workflow. Tests the full pipeline from type mapper through builder to output validation, plus constraint checker integration.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYSTEM, #vhdl-backend |
| Category | Testing |
| Difficulty | 5/5 |
| Status | In Progress |
| Source | `test/03_system/compiler/vhdl_backend_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system tests covering the complete VHDL backend workflow.
Tests the full pipeline from type mapper through builder to output validation,
plus constraint checker integration.

## Related Files
- `src/compiler/backend/vhdl_backend.spl` - Backend orchestrator
- `src/compiler/backend/vhdl_type_mapper.spl` - Type mapping
- `src/compiler/backend/vhdl/vhdl_builder.spl` - Code generation
- `src/compiler/70.backend/vhdl_constraints.spl` - Constraint checking
- `src/app/io/vhdl_ffi.spl` - Toolchain FFI

## Scenarios

### VHDL Pipeline: Type Mapper -> Builder

<details>
<summary>Advanced: generates entity with mapped types</summary>

#### generates entity with mapped types _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port
9. builder emit port end
10. builder emit entity end
11. verify
12. verify
13. verify
14. verify
15. verify
16. verify
17. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
var builder = VhdlBuilder__create("alu")

builder.emit_library_header()
builder.emit_entity_begin("alu")
builder.emit_port_begin()

# Map types and emit ports
val i32_type = mapper.map_primitive(PrimitiveType.I32)
val bool_type = mapper.map_primitive(PrimitiveType.Bool)
val in_dir = mapper.map_port_direction(VhdlPortDirection.In)
val out_dir = mapper.map_port_direction(VhdlPortDirection.Out)

builder.emit_port("a", in_dir, i32_type, false)
builder.emit_port("b", in_dir, i32_type, false)
builder.emit_port("sel", in_dir, bool_type, false)
builder.emit_port("result", out_dir, i32_type, true)
builder.emit_port_end()
builder.emit_entity_end("alu")

val result = builder.build()
verify(result.contains("library ieee;"))
verify(result.contains("entity alu is"))
verify(result.contains("a : in signed(31 downto 0);"))
verify(result.contains("b : in signed(31 downto 0);"))
verify(result.contains("sel : in bit"))
verify(result.contains("result : out signed(31 downto 0)"))
verify(result.contains("end entity alu;"))
```

</details>


</details>

<details>
<summary>Advanced: generates entity with resolved types</summary>

#### generates entity with resolved types _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port
9. builder emit port end
10. builder emit entity end
11. verify
12. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create_resolved()
var builder = VhdlBuilder__create("mux")

builder.emit_library_header()
builder.emit_entity_begin("mux")
builder.emit_port_begin()

val bool_type = mapper.map_primitive(PrimitiveType.Bool)
val u8_type = mapper.map_primitive(PrimitiveType.U8)

builder.emit_port("sel", "in", bool_type, false)
builder.emit_port("a", "in", u8_type, false)
builder.emit_port("b", "in", u8_type, false)
builder.emit_port("y", "out", u8_type, true)
builder.emit_port_end()
builder.emit_entity_end("mux")

val result = builder.build()
verify(result.contains("sel : in std_logic"))
verify(result.contains("a : in unsigned(7 downto 0)"))
```

</details>


</details>

### VHDL Pipeline: Constraints -> Code Generation

<details>
<summary>Advanced: builds validated module output</summary>

#### builds validated module output _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port end
9. builder emit entity end
10. builder emit architecture begin
11. builder emit architecture body begin
12. builder emit signal assign
13. builder emit architecture end
14. verify
15. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = VhdlBuilder__create("validated_mod")
builder.emit_library_header()
builder.emit_entity_begin("validated_mod")
builder.emit_port_begin()
builder.emit_port("a", "in", "signed(31 downto 0)", false)
builder.emit_port("b", "in", "signed(31 downto 0)", false)
builder.emit_port("result", "out", "signed(31 downto 0)", true)
builder.emit_port_end()
builder.emit_entity_end("validated_mod")
builder.emit_architecture_begin("validated_mod", "rtl")
builder.emit_architecture_body_begin()
builder.emit_signal_assign("result", "a + b")
builder.emit_architecture_end("rtl")

val vhdl = builder.build()
verify(vhdl.contains("entity validated_mod is"))
verify(vhdl.contains("result <= a + b;"))
```

</details>


</details>

### VHDL Full Entity Workflows

<details>
<summary>Advanced: generates combinational adder</summary>

#### generates combinational adder _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port end
9. builder emit entity end
10. builder emit architecture begin
11. builder emit architecture body begin
12. builder emit signal assign
13. builder emit architecture end
14. verify
15. verify
16. verify
17. verify
18. verify
19. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
var builder = VhdlBuilder__create("adder")

builder.emit_library_header()
builder.emit_entity_begin("adder")
builder.emit_port_begin()
builder.emit_port("a", "in", mapper.map_signed(32), false)
builder.emit_port("b", "in", mapper.map_signed(32), false)
builder.emit_port("sum", "out", mapper.map_signed(32), true)
builder.emit_port_end()
builder.emit_entity_end("adder")

builder.emit_architecture_begin("adder", "rtl")
builder.emit_architecture_body_begin()
builder.emit_signal_assign("sum", "a + b")
builder.emit_architecture_end("rtl")

val vhdl = builder.build()
verify(vhdl.contains("library ieee;"))
verify(vhdl.contains("use ieee.numeric_std.all;"))
verify(vhdl.contains("entity adder is"))
verify(vhdl.contains("signed(31 downto 0)"))
verify(vhdl.contains("sum <= a + b;"))
verify(vhdl.contains("end architecture rtl;"))
```

</details>


</details>

<details>
<summary>Advanced: generates clocked register</summary>

#### generates clocked register _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit entity begin
4. builder emit port begin
5. builder emit port
6. builder emit port
7. builder emit port
8. builder emit port
9. builder emit port end
10. builder emit entity end
11. builder emit architecture begin
12. builder emit signal decl
13. builder emit architecture body begin
14. builder emit clocked process begin
15. builder emit process body begin
16. builder emit if begin
17. builder emit signal assign
18. builder emit elsif
19. builder emit signal assign
20. builder emit if end
21. builder emit process end
22. builder emit signal assign
23. builder emit architecture end
24. verify
25. verify
26. verify
27. verify
28. verify
29. verify
30. verify
31. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
var builder = VhdlBuilder__create("reg")

builder.emit_library_header()
builder.emit_entity_begin("reg8")
builder.emit_port_begin()
builder.emit_port("clk", "in", mapper.bit_type(), false)
builder.emit_port("rst", "in", mapper.bit_type(), false)
builder.emit_port("d", "in", mapper.map_unsigned(8), false)
builder.emit_port("q", "out", mapper.map_unsigned(8), true)
builder.emit_port_end()
builder.emit_entity_end("reg8")

builder.emit_architecture_begin("reg8", "rtl")
builder.emit_signal_decl("q_reg", mapper.map_unsigned(8), Some("(others => '0')"))
builder.emit_architecture_body_begin()

builder.emit_clocked_process_begin(Some("reg_proc"), "clk", Some("rst"))
builder.emit_process_body_begin()
builder.emit_if_begin("rst = '1'")
builder.emit_signal_assign("q_reg", "(others => '0')")
builder.emit_elsif("rising_edge(clk)")
builder.emit_signal_assign("q_reg", "d")
builder.emit_if_end()
builder.emit_process_end(Some("reg_proc"))

builder.emit_signal_assign("q", "q_reg")
builder.emit_architecture_end("rtl")

val vhdl = builder.build()
verify(vhdl.contains("entity reg8 is"))
verify(vhdl.contains("clk : in bit"))
verify(vhdl.contains("d : in unsigned(7 downto 0)"))
verify(vhdl.contains("signal q_reg : unsigned(7 downto 0) := (others => '0');"))
verify(vhdl.contains("reg_proc: process(clk, rst)"))
verify(vhdl.contains("if rst = '1' then"))
verify(vhdl.contains("elsif rising_edge(clk) then"))
verify(vhdl.contains("q <= q_reg;"))
```

</details>


</details>

<details>
<summary>Advanced: generates FSM with enum states</summary>

#### generates FSM with enum states _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit package begin
4. builder emit type decl
5. builder emit package end
6. builder emit entity begin
7. builder emit port begin
8. builder emit port
9. builder emit port
10. builder emit port
11. builder emit port
12. builder emit port end
13. builder emit entity end
14. verify
15. verify
16. verify
17. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
var builder = VhdlBuilder__create("fsm")

builder.emit_library_header()

# Package with state enum
builder.emit_package_begin("fsm")
val state_enum = mapper.map_enum_type(["Idle", "Running", "Done"])
builder.emit_type_decl("state_t", state_enum)
builder.emit_package_end("fsm")

# Entity
builder.emit_entity_begin("fsm")
builder.emit_port_begin()
builder.emit_port("clk", "in", mapper.bit_type(), false)
builder.emit_port("rst", "in", mapper.bit_type(), false)
builder.emit_port("start", "in", mapper.bit_type(), false)
builder.emit_port("done", "out", mapper.bit_type(), true)
builder.emit_port_end()
builder.emit_entity_end("fsm")

val vhdl = builder.build()
verify(vhdl.contains("package fsm_pkg is"))
verify(vhdl.contains("type state_t is (Idle, Running, Done);"))
verify(vhdl.contains("end package fsm_pkg;"))
verify(vhdl.contains("entity fsm is"))
```

</details>


</details>

<details>
<summary>Advanced: generates entity with record type</summary>

#### generates entity with record type _(slow)_

1. var builder = VhdlBuilder  create
2. builder emit library header
3. builder emit package begin
4. builder emit type decl
5. builder emit package end
6. verify
7. verify
8. verify
9. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
var builder = VhdlBuilder__create("point_module")

builder.emit_library_header()

# Package with record
builder.emit_package_begin("point_module")
val fields = [("x", mapper.map_signed(32)), ("y", mapper.map_signed(32))]
val record_def = mapper.map_record(fields)
builder.emit_type_decl("point_t", record_def)
builder.emit_package_end("point_module")

val vhdl = builder.build()
verify(vhdl.contains("type point_t is record"))
verify(vhdl.contains("x : signed(31 downto 0);"))
verify(vhdl.contains("y : signed(31 downto 0);"))
verify(vhdl.contains("end record;"))
```

</details>


</details>

### VHDL Synthesizability Verification

<details>
<summary>Advanced: accepts all synthesizable integer types</summary>

#### accepts all synthesizable integer types _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
val synth_types = [
    PrimitiveType.I8, PrimitiveType.I16, PrimitiveType.I32, PrimitiveType.I64,
    PrimitiveType.U8, PrimitiveType.U16, PrimitiveType.U32, PrimitiveType.U64,
    PrimitiveType.Bool
]
for ty in synth_types:
    verify(mapper.is_synthesizable(ty))
    val mapped = mapper.map_primitive(ty)
    verify(not mapped.contains("ERROR"))
```

</details>


</details>

<details>
<summary>Advanced: rejects all unsynthesizable float types</summary>

#### rejects all unsynthesizable float types _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
val float_types = [PrimitiveType.F16, PrimitiveType.F32, PrimitiveType.F64]
for ty in float_types:
    verify(not mapper.is_synthesizable(ty))
    val mapped = mapper.map_primitive(ty)
    verify(mapped.contains("ERROR"))
```

</details>


</details>

### VHDL Width Consistency

<details>
<summary>Advanced: width matches mapped type for all integer types</summary>

#### width matches mapped type for all integer types _(slow)_

1. verify
   - Expected: mapper.width_of_type(PrimitiveType.I32) equals `32`
2. verify
   - Expected: mapper.width_of_type(PrimitiveType.U16) equals `16`
3. verify
   - Expected: mapper.width_of_type(PrimitiveType.U8) equals `8`
4. verify
   - Expected: mapper.width_of_type(PrimitiveType.Bool) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper__create()
# I64 -> 64 -> signed(63 downto 0)
expect(mapper.width_of_type(PrimitiveType.I64)).to_equal(64)
verify(mapper.map_primitive(PrimitiveType.I64).contains("63 downto 0"))

# I32 -> 32 -> signed(31 downto 0)
expect(mapper.width_of_type(PrimitiveType.I32)).to_equal(32)
verify(mapper.map_primitive(PrimitiveType.I32).contains("31 downto 0"))

# U16 -> 16 -> unsigned(15 downto 0)
expect(mapper.width_of_type(PrimitiveType.U16)).to_equal(16)
verify(mapper.map_primitive(PrimitiveType.U16).contains("15 downto 0"))

# U8 -> 8 -> unsigned(7 downto 0)
expect(mapper.width_of_type(PrimitiveType.U8)).to_equal(8)
verify(mapper.map_primitive(PrimitiveType.U8).contains("7 downto 0"))

# Bool -> 1
expect(mapper.width_of_type(PrimitiveType.Bool)).to_equal(1)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
