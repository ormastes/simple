# Runtime Layout Verification Specification

> Tests runtime layout verification: compute_layout_verification(), generate_runtime_layout_asserts(), and extract_field_offsets() for @export("C") types. These complement the compile-time _Static_assert checks with runtime assert() calls in spl_verify_layouts().

<!-- sdn-diagram:id=runtime_layout_verification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_layout_verification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_layout_verification_spec -> std
runtime_layout_verification_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_layout_verification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Layout Verification Specification

Tests runtime layout verification: compute_layout_verification(), generate_runtime_layout_asserts(), and extract_field_offsets() for @export("C") types. These complement the compile-time _Static_assert checks with runtime assert() calls in spl_verify_layouts().

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-LAYOUT-002 |
| Category | Compiler / Types / Layout / Runtime |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop — runtime layout safety |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/01_unit/compiler/types/runtime_layout_verification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests runtime layout verification: compute_layout_verification(),
generate_runtime_layout_asserts(), and extract_field_offsets() for
@export("C") types. These complement the compile-time _Static_assert
checks with runtime assert() calls in spl_verify_layouts().

## Key Concepts

| Concept | Description |
|---------|-------------|
| compute_layout_verification | Entry point for runtime verification pipeline |
| generate_runtime_layout_asserts | Emit assert() calls for spl_verify_layouts() |
| extract_field_offsets | Simplified name/offset/size triples |
| FieldOffset | Lightweight offset record for tooling |

## Scenarios

### runtime layout verification

### compute_layout_verification

#### computes correct offsets for a simple struct

1. make field
2. make field
3. make field
4. make field
   - Expected: v.is_valid is true
   - Expected: v.total_size equals `8`
   - Expected: v.alignment equals `4`
   - Expected: v.fields.len() equals `4`
   - Expected: v.fields[0].offset equals `0)  # version`
   - Expected: v.fields[1].offset equals `1)  # flags`
   - Expected: v.fields[2].offset equals `2)  # length`
   - Expected: v.fields[3].offset equals `4)  # sequence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PacketHeader: u8 version, u8 flags, u16 length, u32 sequence
val fields = [
    make_field("version", make_u8_type()),
    make_field("flags", make_u8_type()),
    make_field("length", make_u16_type()),
    make_field("sequence", make_u32_type())
]
val v = compute_layout_verification("PacketHeader", fields, layoutattr_c_repr())
expect(v.is_valid).to_equal(true)
expect(v.total_size).to_equal(8)
expect(v.alignment).to_equal(4)
expect(v.fields.len()).to_equal(4)
expect(v.fields[0].offset).to_equal(0)  # version
expect(v.fields[1].offset).to_equal(1)  # flags
expect(v.fields[2].offset).to_equal(2)  # length
expect(v.fields[3].offset).to_equal(4)  # sequence
```

</details>

#### handles alignment padding

1. make field
2. make field
   - Expected: v.is_valid is true
   - Expected: v.fields[0].offset equals `0)  # a at 0`
   - Expected: v.fields[1].offset equals `4)  # b at 4 (3 bytes padding`
   - Expected: v.total_size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Struct with u8 then u32: padding after u8
val fields = [
    make_field("a", make_u8_type()),
    make_field("b", make_u32_type())
]
val v = compute_layout_verification("Padded", fields, layoutattr_c_repr())
expect(v.is_valid).to_equal(true)
expect(v.fields[0].offset).to_equal(0)  # a at 0
expect(v.fields[1].offset).to_equal(4)  # b at 4 (3 bytes padding)
expect(v.total_size).to_equal(8)
```

</details>

#### computes correct total size with trailing padding

1. make field
2. make field
   - Expected: v.is_valid is true
   - Expected: v.fields[0].offset equals `0)  # big at 0`
   - Expected: v.fields[1].offset equals `8)  # small at 8`
   - Expected: v.total_size equals `16`
   - Expected: v.alignment equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Struct ending with smaller type needs padding to alignment
val fields = [
    make_field("big", make_i64_type()),
    make_field("small", make_i8_type())
]
val v = compute_layout_verification("TailPad", fields, layoutattr_c_repr())
expect(v.is_valid).to_equal(true)
expect(v.fields[0].offset).to_equal(0)  # big at 0
expect(v.fields[1].offset).to_equal(8)  # small at 8
# Total: 9 rounded up to 16 (alignment 8)
expect(v.total_size).to_equal(16)
expect(v.alignment).to_equal(8)
```

</details>

### generate_runtime_layout_asserts

#### generates assert calls for each repr(C) type

1. make field
2. make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i32_type())
]
val v = compute_layout_verification("Point", fields, layoutattr_c_repr())
val asserts = generate_runtime_layout_asserts(v)
# Verify output contains assert(sizeof(...)) and assert(offsetof(...))
expect(asserts).to_contain("assert(sizeof(spl_Point)")
expect(asserts).to_contain("assert(offsetof(spl_Point, x)")
expect(asserts).to_contain("assert(offsetof(spl_Point, y)")
expect(asserts).to_contain("assert(_Alignof(spl_Point)")
```

</details>

#### includes correct numeric values in asserts

1. make field
2. make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_u8_type()),
    make_field("b", make_i32_type())
]
val v = compute_layout_verification("Config", fields, layoutattr_c_repr())
val asserts = generate_runtime_layout_asserts(v)
# size should be 8, offsets 0 and 4
expect(asserts).to_contain("== 8")
expect(asserts).to_contain("== 0")
expect(asserts).to_contain("== 4")
```

</details>

#### generates mismatch description strings

1. make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("value", make_f64_type())
]
val v = compute_layout_verification("Single", fields, layoutattr_c_repr())
val asserts = generate_runtime_layout_asserts(v)
expect(asserts).to_contain("spl_Single size mismatch")
expect(asserts).to_contain("spl_Single.value offset mismatch")
expect(asserts).to_contain("spl_Single alignment mismatch")
```

</details>

#### skips generation when no fields present

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields: [HirField] = []
val v = compute_layout_verification("Empty", fields, layoutattr_c_repr())
val asserts = generate_runtime_layout_asserts(v)
# Still emits sizeof and alignof for the empty struct
expect(asserts).to_contain("sizeof")
# But no offsetof lines
expect(asserts).to_not_contain("offsetof")
```

</details>

### extract_field_offsets

#### extracts name, offset, size for each field

1. make field
2. make field
3. make field
4. make field
   - Expected: offsets.len() equals `4`
   - Expected: offsets[0].name equals `version`
   - Expected: offsets[0].offset equals `0`
   - Expected: offsets[0].size equals `1`
   - Expected: offsets[1].name equals `flags`
   - Expected: offsets[1].offset equals `1`
   - Expected: offsets[1].size equals `1`
   - Expected: offsets[2].name equals `length`
   - Expected: offsets[2].offset equals `2`
   - Expected: offsets[2].size equals `2`
   - Expected: offsets[3].name equals `sequence`
   - Expected: offsets[3].offset equals `4`
   - Expected: offsets[3].size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("version", make_u8_type()),
    make_field("flags", make_u8_type()),
    make_field("length", make_u16_type()),
    make_field("sequence", make_u32_type())
]
val v = compute_layout_verification("PacketHeader", fields, layoutattr_c_repr())
val offsets = extract_field_offsets(v)
expect(offsets.len()).to_equal(4)
expect(offsets[0].name).to_equal("version")
expect(offsets[0].offset).to_equal(0)
expect(offsets[0].size).to_equal(1)
expect(offsets[1].name).to_equal("flags")
expect(offsets[1].offset).to_equal(1)
expect(offsets[1].size).to_equal(1)
expect(offsets[2].name).to_equal("length")
expect(offsets[2].offset).to_equal(2)
expect(offsets[2].size).to_equal(2)
expect(offsets[3].name).to_equal("sequence")
expect(offsets[3].offset).to_equal(4)
expect(offsets[3].size).to_equal(4)
```

</details>

#### returns empty list for empty struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields: [HirField] = []
val v = compute_layout_verification("Empty", fields, layoutattr_c_repr())
val offsets = extract_field_offsets(v)
expect(offsets.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [SFFI bidirectional class interop — runtime layout safety](SFFI bidirectional class interop — runtime layout safety)
- **Plan:** [parsed-questing-goose.md](parsed-questing-goose.md)
- **Design:** [sffi_external_library_pattern.md](sffi_external_library_pattern.md)


</details>
