# Layout Verification Specification

> Tests struct layout computation, C ABI layout rules, _Static_assert generation, and C struct definition generation for @export("C") types.

<!-- sdn-diagram:id=layout_verification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_verification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_verification_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_verification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Verification Specification

Tests struct layout computation, C ABI layout rules, _Static_assert generation, and C struct definition generation for @export("C") types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-LAYOUT-001 |
| Category | Compiler / Types / Layout |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop — struct layout safety |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/01_unit/compiler/types/layout_verification_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests struct layout computation, C ABI layout rules, _Static_assert generation,
and C struct definition generation for @export("C") types.

## Key Concepts

| Concept | Description |
|---------|-------------|
| TypeLayout | Computed struct layout: size, align, fields, stride |
| FieldLayout | Per-field: name, offset, size, alignment |
| verify_c_layout | Compute + verify C-compatible layout |
| generate_c_static_asserts | Emit _Static_assert for headers |
| generate_c_struct_def | Emit typedef struct for headers |

## Scenarios

### Layout Verification

### primitive sizes

#### i8 is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("i8")
expect(s.?).to_equal(true)
expect(s ?? 0).to_equal(1)
```

</details>

#### i32 is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("i32")
expect(s.?).to_equal(true)
expect(s ?? 0).to_equal(4)
```

</details>

#### i64 is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("i64")
expect(s.?).to_equal(true)
expect(s ?? 0).to_equal(8)
```

</details>

#### f64 is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("f64")
expect(s.?).to_equal(true)
expect(s ?? 0).to_equal(8)
```

</details>

#### bool is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("bool")
expect(s.?).to_equal(true)
expect(s ?? 0).to_equal(1)
```

</details>

#### returns nil for unknown type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = primitive_size("unknown_type")
expect(s.?).to_equal(false)
```

</details>

### primitive alignment

#### i8 aligns to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = primitive_align("i8")
expect(a ?? 0).to_equal(1)
```

</details>

#### i32 aligns to 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = primitive_align("i32")
expect(a ?? 0).to_equal(4)
```

</details>

#### i64 aligns to 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = primitive_align("i64")
expect(a ?? 0).to_equal(8)
```

</details>

### C layout computation

#### computes correct size for simple struct (i32, i32)

- make field
- make field
   - Expected: layout.size equals `8`
   - Expected: layout.align equals `4`
   - Expected: layout.fields.len() equals `2`
   - Expected: layout.fields[0].offset equals `0`
   - Expected: layout.fields[1].offset equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i32_type())
]
val layout = compute_struct_layout(fields, layoutattr_c_repr())
expect(layout.size).to_equal(8)
expect(layout.align).to_equal(4)
expect(layout.fields.len()).to_equal(2)
expect(layout.fields[0].offset).to_equal(0)
expect(layout.fields[1].offset).to_equal(4)
```

</details>

#### adds padding for alignment (i8, i32)

- make field
- make field
   - Expected: layout.fields[0].offset equals `0`
   - Expected: layout.fields[1].offset equals `4`
   - Expected: layout.size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i8_type()),
    make_field("b", make_i32_type())
]
val layout = compute_struct_layout(fields, layoutattr_c_repr())
# i8 at offset 0 (1 byte), then 3 bytes padding, i32 at offset 4
expect(layout.fields[0].offset).to_equal(0)
expect(layout.fields[1].offset).to_equal(4)
# Total: 4 + 4 = 8 bytes
expect(layout.size).to_equal(8)
```

</details>

#### computes max alignment for struct

- make field
- make field
   - Expected: layout.align equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i8_type()),
    make_field("b", make_i64_type())
]
val layout = compute_struct_layout(fields, layoutattr_c_repr())
# Max alignment is 8 (from i64)
expect(layout.align).to_equal(8)
```

</details>

#### handles empty field list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields: [HirField] = []
val layout = compute_struct_layout(fields, layoutattr_c_repr())
expect(layout.size).to_equal(0)
expect(layout.fields.len()).to_equal(0)
```

</details>

#### pads struct size to alignment boundary

- make field
- make field
   - Expected: layout.fields[0].offset equals `0`
   - Expected: layout.fields[1].offset equals `8`
   - Expected: layout.size equals `16`
   - Expected: layout.align equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i64_type()),
    make_field("b", make_i8_type())
]
val layout = compute_struct_layout(fields, layoutattr_c_repr())
# i64 at offset 0 (8 bytes), i8 at offset 8 (1 byte)
# Total data: 9, but struct align is 8, so padded to 16
expect(layout.fields[0].offset).to_equal(0)
expect(layout.fields[1].offset).to_equal(8)
expect(layout.size).to_equal(16)
expect(layout.align).to_equal(8)
```

</details>

### packed layout

#### packs fields without padding

- make field
- make field
   - Expected: layout.fields[0].offset equals `0`
   - Expected: layout.fields[1].offset equals `1`
   - Expected: layout.size equals `5`
   - Expected: layout.align equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i8_type()),
    make_field("b", make_i32_type())
]
val layout = compute_struct_layout(fields, layoutattr_packed())
expect(layout.fields[0].offset).to_equal(0)
expect(layout.fields[1].offset).to_equal(1)
expect(layout.size).to_equal(5)
expect(layout.align).to_equal(1)
```

</details>

### alignment helpers

#### align_up rounds up correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(align_up(1, 4)).to_equal(4)
expect(align_up(4, 4)).to_equal(4)
expect(align_up(5, 4)).to_equal(8)
expect(align_up(0, 8)).to_equal(0)
```

</details>

#### is_aligned checks correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_aligned(0, 4)).to_equal(true)
expect(is_aligned(4, 4)).to_equal(true)
expect(is_aligned(3, 4)).to_equal(false)
expect(is_aligned(8, 8)).to_equal(true)
```

</details>

#### is_power_of_two validates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_power_of_two(1)).to_equal(true)
expect(is_power_of_two(2)).to_equal(true)
expect(is_power_of_two(4)).to_equal(true)
expect(is_power_of_two(8)).to_equal(true)
expect(is_power_of_two(3)).to_equal(false)
expect(is_power_of_two(0)).to_equal(false)
```

</details>

### verify_c_layout

#### verifies simple struct is valid

- make field
- make field
   - Expected: v.is_valid is true
   - Expected: v.class_name equals `Point`
   - Expected: v.total_size equals `8`
   - Expected: v.alignment equals `4`
   - Expected: v.mismatches.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i32_type())
]
val v = verify_c_layout("Point", fields, layoutattr_c_repr())
expect(v.is_valid).to_equal(true)
expect(v.class_name).to_equal("Point")
expect(v.total_size).to_equal(8)
expect(v.alignment).to_equal(4)
expect(v.mismatches.len()).to_equal(0)
```

</details>

#### computes correct field offsets with padding

- make field
- make field
- make field
   - Expected: v.is_valid is true
   - Expected: v.fields[0].offset equals `0)   # version at 0`
   - Expected: v.fields[1].offset equals `1)   # flags at 1`
   - Expected: v.fields[2].offset equals `4)   # length at 4 (after 2 bytes padding`
   - Expected: v.total_size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("version", make_u8_type()),
    make_field("flags", make_u8_type()),
    make_field("length", make_i32_type())
]
val v = verify_c_layout("PacketHeader", fields, layoutattr_c_repr())
expect(v.is_valid).to_equal(true)
expect(v.fields[0].offset).to_equal(0)   # version at 0
expect(v.fields[1].offset).to_equal(1)   # flags at 1
expect(v.fields[2].offset).to_equal(4)   # length at 4 (after 2 bytes padding)
expect(v.total_size).to_equal(8)
```

</details>

### _Static_assert generation

#### generates sizeof assert

- make field
- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i32_type())
]
val v = verify_c_layout("Point", fields, layoutattr_c_repr())
val asserts = generate_c_static_asserts(v)
expect(asserts).to_contain("_Static_assert")
expect(asserts).to_contain("sizeof")
expect(asserts).to_contain("spl_Point")
expect(asserts).to_contain("8")
```

</details>

#### generates offsetof asserts for each field

- make field
- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i32_type())
]
val v = verify_c_layout("Point", fields, layoutattr_c_repr())
val asserts = generate_c_static_asserts(v)
expect(asserts).to_contain("offsetof")
expect(asserts).to_contain("spl_Point")
expect(asserts).to_contain("x")
expect(asserts).to_contain("y")
```

</details>

#### generates alignment assert

- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i64_type())
]
val v = verify_c_layout("Aligned", fields, layoutattr_c_repr())
val asserts = generate_c_static_asserts(v)
expect(asserts).to_contain("_Alignof")
```

</details>

#### skips offsetof asserts for explicit bitfields

- make bits field
- make bits field
   - Expected: asserts does not contain `offsetof(spl_Flags, mode)`
   - Expected: asserts does not contain `offsetof(spl_Flags, speed)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_bits_field("mode", make_u8_type(), 4),
    make_bits_field("speed", make_u8_type(), 2)
]
val v = verify_c_layout("Flags", fields, layoutattr_c_repr())
val asserts = generate_c_static_asserts(v)
expect(asserts).to_contain("sizeof")
expect(asserts.contains("offsetof(spl_Flags, mode)")).to_equal(false)
expect(asserts.contains("offsetof(spl_Flags, speed)")).to_equal(false)
```

</details>

### C struct definition

#### generates valid C typedef struct

- make field
- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("precision", make_i32_type()),
    make_field("value", make_f64_type())
]
val v = verify_c_layout("Calculator", fields, layoutattr_c_repr())
val c_def = generate_c_struct_def(v)
expect(c_def).to_contain("typedef struct spl_Calculator")
expect(c_def).to_contain("precision")
expect(c_def).to_contain("value")
expect(c_def).to_contain("} spl_Calculator;")
```

</details>

#### generates struct with correct field types

- make field
- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("flag", make_bool_type()),
    make_field("count", make_i32_type())
]
val v = verify_c_layout("Config", fields, layoutattr_c_repr())
val c_def = generate_c_struct_def(v)
expect(c_def).to_contain("uint8_t")  # bool maps to uint8_t
expect(c_def).to_contain("int32_t")  # i32 maps to int32_t
```

</details>

#### generates C bitfield syntax for explicit bit widths

- make bits field
- make bits field
- make bits field
- make bits field
   - Expected: v.total_size equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_bits_field("mode", make_u8_type(), 4),
    make_bits_field("output", make_bool_type(), 1),
    make_bits_field("input", make_bool_type(), 1),
    make_bits_field("speed", make_u8_type(), 2)
]
val v = verify_c_layout("GpioRegister", fields, layoutattr_c_repr())
val c_def = generate_c_struct_def(v)
expect(v.total_size).to_equal(1)
expect(c_def).to_contain("uint8_t mode : 4;")
expect(c_def).to_contain("uint8_t output : 1;")
expect(c_def).to_contain("uint8_t input : 1;")
expect(c_def).to_contain("uint8_t speed : 2;")
```

</details>

### padding computation

#### computes zero padding for tightly packed fields

- make field
- make field
   - Expected: padding equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i32_type()),
    make_field("b", make_i32_type())
]
val v = verify_c_layout("Tight", fields, layoutattr_c_repr())
val padding = compute_padding_bytes(v)
expect(padding).to_equal(0)
```

</details>

#### computes padding bytes for misaligned struct

- make field
- make field
   - Expected: padding equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i8_type()),
    make_field("b", make_i32_type())
]
val v = verify_c_layout("Padded", fields, layoutattr_c_repr())
val padding = compute_padding_bytes(v)
# Total size 8, data bytes 5 (1 + 4), padding = 3
expect(padding).to_equal(3)
```

</details>

#### computes tail padding

- make field
- make field
   - Expected: padding equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_i64_type()),
    make_field("b", make_i8_type())
]
val v = verify_c_layout("TailPad", fields, layoutattr_c_repr())
val padding = compute_padding_bytes(v)
# Total size 16, data bytes 9 (8 + 1), padding = 7
expect(padding).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [SFFI bidirectional class interop — struct layout safety](SFFI bidirectional class interop — struct layout safety)
- **Plan:** [parsed-questing-goose.md](parsed-questing-goose.md)
- **Design:** [sffi_external_library_pattern.md](sffi_external_library_pattern.md)


</details>
