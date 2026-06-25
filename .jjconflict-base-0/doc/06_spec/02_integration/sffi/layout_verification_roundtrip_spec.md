# SFFI Layout Verification Round-Trip Proof

> Tests ABI/layout verification across the SFFI boundary:

<!-- sdn-diagram:id=layout_verification_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_verification_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_verification_roundtrip_spec -> std
layout_verification_roundtrip_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_verification_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI Layout Verification Round-Trip Proof

Tests ABI/layout verification across the SFFI boundary:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-BIDIR-WS7 |
| Category | Compiler Integration / SFFI |
| Status | End-to-End Proof |
| Source | `test/02_integration/sffi/layout_verification_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests ABI/layout verification across the SFFI boundary:

1. **Layout computation** -- `verify_c_layout` computes field offsets and sizes
   using C alignment rules for `@repr("C")` structs.
2. **Static assert generation** -- `generate_c_static_asserts` emits
   `_Static_assert` statements that gcc can compile to verify layout agreement.
3. **Positive test** -- Well-aligned struct produces `_Static_assert` that
   compiles cleanly with `gcc -c`.
4. **Negative test** -- Deliberately wrong `_Static_assert` causes compilation
   failure, proving the assertions are meaningful.
5. **Cross-architecture** -- Layout computation for different target
   architectures produces consistent results.

Requires: gcc (or cc) on the host system. Tests skip gracefully if unavailable.

## Scenarios

### SFFI Layout Verification Round-Trip

### layout computation

#### computes correct layout for simple u8-only struct

1. make field
2. make field
3. make field
4. layoutattr c repr
   - Expected: verification.is_valid is true
   - Expected: verification.total_size equals `3`
   - Expected: verification.alignment equals `1`
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `1`
   - Expected: verification.fields[2].offset equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Flags",
    [
        make_field("a", make_u8_type()),
        make_field("b", make_u8_type()),
        make_field("c", make_u8_type())
    ],
    layoutattr_c_repr()
)

expect(verification.is_valid).to_equal(true)
expect(verification.total_size).to_equal(3)
expect(verification.alignment).to_equal(1)
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(1)
expect(verification.fields[2].offset).to_equal(2)
```

</details>

#### computes correct layout with padding for mixed types

1. make field
2. make field
3. make field
4. layoutattr c repr
   - Expected: verification.is_valid is true
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `4`
   - Expected: verification.fields[2].offset equals `8`
   - Expected: verification.total_size equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Mixed",
    [
        make_field("flag", make_u8_type()),
        make_field("value", make_i32_type()),
        make_field("tag", make_u8_type())
    ],
    layoutattr_c_repr()
)

expect(verification.is_valid).to_equal(true)
# u8 at 0, padding 1-3, i32 at 4, u8 at 8, padding 9-11
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(4)
expect(verification.fields[2].offset).to_equal(8)
expect(verification.total_size).to_equal(12)
```

</details>

#### computes correct layout for network packet header

1. make field
2. make field
3. make field
4. make field
5. layoutattr c repr
   - Expected: verification.is_valid is true
   - Expected: verification.total_size equals `8`
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `1`
   - Expected: verification.fields[2].offset equals `2`
   - Expected: verification.fields[3].offset equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "PacketHeader",
    [
        make_field("version", make_u8_type()),
        make_field("flags", make_u8_type()),
        make_field("length", make_u16_type()),
        make_field("sequence", make_u32_type())
    ],
    layoutattr_c_repr()
)

expect(verification.is_valid).to_equal(true)
expect(verification.total_size).to_equal(8)
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(1)
expect(verification.fields[2].offset).to_equal(2)
expect(verification.fields[3].offset).to_equal(4)
```

</details>

#### computes correct layout for struct with f64 requiring 8-byte align

1. make field
2. make field
3. layoutattr c repr
   - Expected: verification.is_valid is true
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `8`
   - Expected: verification.total_size equals `16`
   - Expected: verification.alignment equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Measurement",
    [
        make_field("id", make_i32_type()),
        make_field("value", make_f64_type())
    ],
    layoutattr_c_repr()
)

expect(verification.is_valid).to_equal(true)
# i32 at 0, padding 4-7, f64 at 8
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(8)
expect(verification.total_size).to_equal(16)
expect(verification.alignment).to_equal(8)
```

</details>

#### computes correct layout for struct with i64 field

1. make field
2. make field
3. layoutattr c repr
   - Expected: verification.is_valid is true
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `8`
   - Expected: verification.total_size equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Counter",
    [
        make_field("tag", make_u8_type()),
        make_field("count", make_i64_type())
    ],
    layoutattr_c_repr()
)

expect(verification.is_valid).to_equal(true)
# u8 at 0, padding 1-7, i64 at 8
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(8)
expect(verification.total_size).to_equal(16)
```

</details>

### static assert generation

#### generates _Static_assert for C with correct size and offsets

1. make field
2. make field
3. make field
4. make field
5. layoutattr c repr


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "PacketHeader",
    [
        make_field("version", make_u8_type()),
        make_field("flags", make_u8_type()),
        make_field("length", make_u16_type()),
        make_field("sequence", make_u32_type())
    ],
    layoutattr_c_repr()
)

val asserts = generate_c_static_asserts(verification)
expect(asserts).to_contain("_Static_assert")
expect(asserts).to_contain("sizeof(spl_PacketHeader)")
expect(asserts).to_contain("== 8")
expect(asserts).to_contain("offsetof")
expect(asserts).to_contain("version")
expect(asserts).to_contain("sequence")
```

</details>

#### generates static_assert for C++ with correct size and offsets

1. make field
2. make field
3. layoutattr c repr


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Sensor",
    [
        make_field("id", make_i32_type()),
        make_field("reading", make_f64_type())
    ],
    layoutattr_c_repr()
)

val asserts = generate_cpp_static_asserts(verification)
expect(asserts).to_contain("static_assert")
expect(asserts).to_contain("sizeof(spl_Sensor)")
expect(asserts).to_contain("== 16")
```

</details>

#### generates C struct definition matching computed layout

1. make field
2. make field
3. layoutattr c repr


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "Point",
    [
        make_field("x", make_f64_type()),
        make_field("y", make_f64_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)
expect(struct_def).to_contain("typedef struct")
expect(struct_def).to_contain("spl_Point")
expect(struct_def).to_contain("double x")
expect(struct_def).to_contain("double y")
```

</details>

### alignment utilities

#### aligns values up to alignment boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(align_up(0, 4)).to_equal(0)
expect(align_up(1, 4)).to_equal(4)
expect(align_up(3, 4)).to_equal(4)
expect(align_up(4, 4)).to_equal(4)
expect(align_up(5, 4)).to_equal(8)
expect(align_up(7, 8)).to_equal(8)
expect(align_up(8, 8)).to_equal(8)
expect(align_up(9, 8)).to_equal(16)
```

</details>

#### checks alignment correctness

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_aligned(0, 4)).to_equal(true)
expect(is_aligned(4, 4)).to_equal(true)
expect(is_aligned(8, 4)).to_equal(true)
expect(is_aligned(1, 4)).to_equal(false)
expect(is_aligned(3, 4)).to_equal(false)
expect(is_aligned(8, 8)).to_equal(true)
expect(is_aligned(7, 8)).to_equal(false)
```

</details>

#### validates power-of-two checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_power_of_two(1)).to_equal(true)
expect(is_power_of_two(2)).to_equal(true)
expect(is_power_of_two(4)).to_equal(true)
expect(is_power_of_two(8)).to_equal(true)
expect(is_power_of_two(16)).to_equal(true)
expect(is_power_of_two(3)).to_equal(false)
expect(is_power_of_two(6)).to_equal(false)
expect(is_power_of_two(0)).to_equal(false)
```

</details>

### gcc compilation of static asserts (positive)

#### compiles correct _Static_assert with gcc successfully

1. make field
2. make field
3. make field
4. make field
5. layoutattr c repr
6. "int main
7. assert ok
8. print
9. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

# Build a verification for a simple struct and generate asserts
val verification = verify_c_layout(
    "PacketHeader",
    [
        make_field("version", make_u8_type()),
        make_field("flags", make_u8_type()),
        make_field("length", make_u16_type()),
        make_field("sequence", make_u32_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)
val asserts = generate_c_static_asserts(verification)

# Build a C source that includes the struct + asserts
val c_source = TEST_DIR + "/layout_check.c"
val c_code = "#include <stdint.h>" + NL +
    "#include <stddef.h>" + NL +
    NL +
    struct_def + NL +
    NL +
    asserts + NL +
    NL +
    "int main(void) { return 0; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write positive layout fixture")

val cc = c_compiler()
val (out, err, code) = rt_process_run(cc, [
    "-c", "-std=c11",
    "-o", TEST_DIR + "/layout_check.o",
    c_source
])

if code != 0:
    print("gcc stdout: " + out)
    print("gcc stderr: " + err)
expect(code).to_equal(0)
```

</details>

#### compiles layout check for struct with padding

1. make field
2. make field
3. make field
4. layoutattr c repr
5. "int main
6. assert ok
7. print
8. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val verification = verify_c_layout(
    "PaddedStruct",
    [
        make_field("flag", make_u8_type()),
        make_field("value", make_i32_type()),
        make_field("tag", make_u8_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)
val asserts = generate_c_static_asserts(verification)

val c_source = TEST_DIR + "/padded_check.c"
val c_code = "#include <stdint.h>" + NL +
    "#include <stddef.h>" + NL +
    NL +
    struct_def + NL +
    NL +
    asserts + NL +
    NL +
    "int main(void) { return 0; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write padded layout fixture")

val cc = c_compiler()
val (out, err, code) = rt_process_run(cc, [
    "-c", "-std=c11",
    "-o", TEST_DIR + "/padded_check.o",
    c_source
])

if code != 0:
    print("gcc stdout: " + out)
    print("gcc stderr: " + err)
expect(code).to_equal(0)
```

</details>

#### compiles layout check for struct with f64 alignment

1. make field
2. make field
3. layoutattr c repr
4. "int main
5. assert ok
6. print
7. print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val verification = verify_c_layout(
    "Sensor",
    [
        make_field("id", make_i32_type()),
        make_field("reading", make_f64_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)
val asserts = generate_c_static_asserts(verification)

val c_source = TEST_DIR + "/sensor_check.c"
val c_code = "#include <stdint.h>" + NL +
    "#include <stddef.h>" + NL +
    NL +
    struct_def + NL +
    NL +
    asserts + NL +
    NL +
    "int main(void) { return 0; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write sensor layout fixture")

val cc = c_compiler()
val (out, err, code) = rt_process_run(cc, [
    "-c", "-std=c11",
    "-o", TEST_DIR + "/sensor_check.o",
    c_source
])

if code != 0:
    print("gcc stdout: " + out)
    print("gcc stderr: " + err)
expect(code).to_equal(0)
```

</details>

### gcc compilation of static asserts (negative)

#### fails when _Static_assert has deliberately wrong size

1. make field
2. make field
3. layoutattr c repr
4. " Static assert
5. "int main
6. assert ok
   - Expected: "bad size static assert should fail compilation" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val verification = verify_c_layout(
    "BadSize",
    [
        make_field("x", make_i32_type()),
        make_field("y", make_i32_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)

# Deliberately write WRONG size assert (claiming 4 bytes instead of 8)
val c_source = TEST_DIR + "/bad_size_check.c"
val c_code = "#include <stdint.h>" + NL +
    "#include <stddef.h>" + NL +
    NL +
    struct_def + NL +
    NL +
    "_Static_assert(sizeof(spl_BadSize) == 4, \"deliberately wrong size\");" + NL +
    NL +
    "int main(void) { return 0; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write bad-size fixture")

val cc = c_compiler()
val (_out, _err, code) = rt_process_run(cc, [
    "-c", "-std=c11",
    "-o", TEST_DIR + "/bad_size_check.o",
    c_source
])

# Should FAIL compilation -- wrong size
if code == 0:
    expect("bad size static assert should fail compilation").to_equal("")
expect(c_source).to_end_with(".c")
```

</details>

#### fails when _Static_assert has deliberately wrong offset

1. make field
2. make field
3. layoutattr c repr
4. " Static assert
5. "int main
6. assert ok
   - Expected: "bad offset static assert should fail compilation" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not has_c_compiler():
    return "skip: no C compiler available"

val verification = verify_c_layout(
    "BadOffset",
    [
        make_field("tag", make_u8_type()),
        make_field("value", make_i32_type())
    ],
    layoutattr_c_repr()
)

val struct_def = generate_c_struct_def(verification)

# Deliberately write WRONG offset (claiming value is at offset 1 instead of 4)
val c_source = TEST_DIR + "/bad_offset_check.c"
val c_code = "#include <stdint.h>" + NL +
    "#include <stddef.h>" + NL +
    NL +
    struct_def + NL +
    NL +
    "_Static_assert(offsetof(spl_BadOffset, value) == 1, \"deliberately wrong offset\");" + NL +
    NL +
    "int main(void) { return 0; }" + NL

assert_ok(write_source(c_source, c_code), "failed to write bad-offset fixture")

val cc = c_compiler()
val (_out, _err, code) = rt_process_run(cc, [
    "-c", "-std=c11",
    "-o", TEST_DIR + "/bad_offset_check.o",
    c_source
])

# Should FAIL compilation -- wrong offset
if code == 0:
    expect("bad offset static assert should fail compilation").to_equal("")
expect(c_source).to_end_with(".c")
```

</details>

### bitfield layout verification

#### computes layout for struct with @bits fields

1. make bits field
2. make bits field
3. make bits field
4. make bits field
5. layoutattr c repr
   - Expected: "bitfield layout verification should be valid" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verification = verify_c_layout(
    "GpioRegister",
    [
        make_bits_field("mode", make_u8_type(), 4),
        make_bits_field("output", make_bool_type(), 1),
        make_bits_field("input", make_bool_type(), 1),
        make_bits_field("speed", make_u8_type(), 2)
    ],
    layoutattr_c_repr()
)

if not verification.is_valid:
    expect("bitfield layout verification should be valid").to_equal("")
# All bitfields fit in a single byte (4+1+1+2 = 8 bits)
expect(verification.total_size).to_be_less_than(5)
```

</details>

### packed layout

#### packed struct has no padding between fields

1. make field
2. make field
3. make field
   - Expected: verification.is_valid is true
   - Expected: verification.fields[0].offset equals `0`
   - Expected: verification.fields[1].offset equals `1`
   - Expected: verification.fields[2].offset equals `5`
   - Expected: verification.total_size equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packed_attr = layoutattr_packed()
val verification = verify_c_layout(
    "PackedData",
    [
        make_field("flag", make_u8_type()),
        make_field("value", make_i32_type()),
        make_field("tag", make_u8_type())
    ],
    packed_attr
)

expect(verification.is_valid).to_equal(true)
# Packed: u8(1) + i32(4) + u8(1) = 6 bytes, no padding
expect(verification.fields[0].offset).to_equal(0)
expect(verification.fields[1].offset).to_equal(1)
expect(verification.fields[2].offset).to_equal(5)
expect(verification.total_size).to_equal(6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
