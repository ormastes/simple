# Vhdl Type Mapper Specification

> <details>

<!-- sdn-diagram:id=vhdl_type_mapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_type_mapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_type_mapper_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_type_mapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Type Mapper Specification

## Scenarios

### Vhdl Type Mapper

#### maps primitive numeric and boolean types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val resolved = VhdlTypeMapper.create_resolved()

expect(mapper.map_primitive(PrimitiveType.I64)).to_equal("signed(63 downto 0)")
expect(mapper.map_primitive(PrimitiveType.U8)).to_equal("unsigned(7 downto 0)")
expect(mapper.map_primitive(PrimitiveType.Bool)).to_equal("bit")
expect(resolved.map_primitive(PrimitiveType.Bool)).to_equal("std_logic")
```

</details>

#### marks floating point types as unsynthesizable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()

expect(mapper.map_primitive(PrimitiveType.F32)).to_contain("ERROR")
expect(mapper.map_primitive(PrimitiveType.F64)).to_contain("ERROR")
expect(mapper.is_synthesizable(PrimitiveType.F64)).to_equal(false)
```

</details>

#### reports precise unsupported primitive diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()

expect(mapper.unsupported_primitive_diagnostic(PrimitiveType.F16, "constant emission").unwrap()).to_contain("f16")
expect(mapper.unsupported_primitive_diagnostic(PrimitiveType.F32, "port emission").unwrap()).to_contain("fixed-point or integer lowering")
expect(mapper.unsupported_primitive_diagnostic(PrimitiveType.F64, "type emission").unwrap()).to_contain("before VHDL emission")
expect(mapper.unsupported_primitive_diagnostic(PrimitiveType.Unit, "local signal").unwrap()).to_contain("no VHDL signal")
expect(mapper.unsupported_primitive_diagnostic(PrimitiveType.I32, "type emission").?).to_equal(false)
```

</details>

#### maps VHDL helper types deterministically

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()

expect(mapper.map_signed(16)).to_equal("signed(15 downto 0)")
expect(mapper.map_unsigned(9)).to_equal("unsigned(8 downto 0)")
expect(mapper.map_fixed_bits(17, false)).to_equal("unsigned(16 downto 0)")
expect(mapper.map_fixed_bits(17, true)).to_equal("signed(16 downto 0)")
expect(mapper.map_std_logic_vector(8)).to_equal("std_logic_vector(7 downto 0)")
expect(mapper.map_integer_range(-1, 7)).to_equal("integer range -1 to 7")
expect(mapper.map_port_direction(VhdlPortDirection.Buffer)).to_equal("buffer")
expect(mapper.fixed_width_diagnostic(0).?).to_equal(true)
expect(mapper.fixed_width_diagnostic(1).?).to_equal(false)
```

</details>

#### maps record, enum, and array forms

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()
val record = mapper.map_record([("x", "signed(31 downto 0)")])

expect(record).to_contain("record")
expect(record).to_contain("x : signed(31 downto 0);")
expect(record).to_contain("end record")
expect(mapper.map_enum_type(["Idle", "Done"])).to_equal("(Idle, Done)")
expect(mapper.payload_enum_diagnostic("maybe_t", "Some", "aggregate lowering")).to_contain("Payload enum `maybe_t.Some`")
expect(mapper.payload_enum_diagnostic("maybe_t", "Some", "aggregate lowering")).to_contain("tagged-record lowering is not implemented")
expect(mapper.map_array_type("bit", 4)).to_equal("array (0 to 3) of bit")
```

</details>

#### reports widths and bit sizes for MIR types

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = VhdlTypeMapper.create()

expect(mapper.width_of_type(PrimitiveType.Bool)).to_equal(1)
expect(mapper.size_of(MirType.i64())).to_equal(64)
expect(mapper.size_of(MirType.bits(13))).to_equal(13)
expect(mapper.size_of(MirType.sbits(21))).to_equal(21)
expect(mapper.size_of(MirType(kind: MirTypeKind.Array(MirType.i64(), 2)))).to_equal(128)
expect(mapper.align_of(MirType.i64())).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_type_mapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vhdl Type Mapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
