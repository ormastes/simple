# SFFI Lint Rules Specification

> Tests the five SFFI lint rules that validate @export("C") classes have C-compatible layouts and types:

<!-- sdn-diagram:id=sffi_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sffi_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sffi_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sffi_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFFI Lint Rules Specification

Tests the five SFFI lint rules that validate @export("C") classes have C-compatible layouts and types:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-LINT-001..005 |
| Category | Compiler / Semantics / Lint |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop — layout safety |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/01_unit/compiler/semantics/sffi_lint_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the five SFFI lint rules that validate @export("C") classes have
C-compatible layouts and types:
- SFFI001: Non-C-compatible field type (ERROR)
- SFFI002: text field needs marshalling (WARNING)
- SFFI003: Missing @repr("C") layout (ERROR)
- SFFI004: Bitfield without explicit width (ERROR)
- SFFI005: Platform-dependent type size (WARNING)

## Key Concepts

| Concept | Description |
|---------|-------------|
| SffiLintWarning | Lint diagnostic with code, severity, message, hint |
| lint_sffi_export | Main entry — runs all checks on a HirClass |
| C-compatible | i8..i64, u8..u64, f32, f64, bool, Ptr |

## Scenarios

### SFFI Lint Rules

### SFFI001 - C-compatible types

#### passes for i32, i64, f64, bool fields

- make field
- make field
- make field
- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_i64_type()),
    make_field("z", make_f64_type()),
    make_field("flag", make_bool_type())
]
val cls = make_exported_class("Point", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### errors for List field

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI001`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("items", make_array_type())
]
val cls = make_exported_class("BadClass", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI001")
expect(warnings[0].severity).to_equal("ERROR")
```

</details>

#### errors for Dict field

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI001`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("data", make_dict_type())
]
val cls = make_exported_class("BadClass", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI001")
expect(warnings[0].severity).to_equal("ERROR")
```

</details>

#### errors for Option field

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI001`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("maybe", make_optional_type())
]
val cls = make_exported_class("BadClass", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI001")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("Optional")
```

</details>

#### errors for captured Function field

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("callback", make_capturing_function_type())
]
val cls = make_exported_class("BadClass", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI001")
expect(warnings[0].message).to_contain("closure")
```

</details>

#### reports multiple errors for multiple non-C fields

- make field
- make field
- make field
   - Expected: warnings.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("items", make_array_type()),
    make_field("data", make_dict_type()),
    make_field("ok_field", make_i32_type())
]
val cls = make_exported_class("BadClass", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(2)
```

</details>

#### passes for transparent custom primitive fields

- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fd_type = make_custom_primitive_i64_type("SffiFd", 9001)
val fields = [
    make_field("fd", fd_type)
]
val cls = make_exported_class("FdWrapper", fields, true)
val warnings = check_sffi001_c_compatible_types(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### SFFI002 - text field warning

#### warns for text field in exported class

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI002`
   - Expected: warnings[0].severity equals `WARNING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("name", make_str_type())
]
val cls = make_exported_class("Person", fields, true)
val warnings = check_sffi002_text_field(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI002")
expect(warnings[0].severity).to_equal("WARNING")
expect(warnings[0].message).to_contain("text")
```

</details>

#### no warning for non-text fields

- make field
- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_f64_type())
]
val cls = make_exported_class("Point", fields, true)
val warnings = check_sffi002_text_field(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### SFFI003 - repr(C) required

#### errors when @export(C) without @repr(C)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [make_field("x", make_i32_type())]
val cls = make_exported_class("BadLayout", fields, false)
val warnings = check_sffi003_repr_required(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI003")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("@repr")
```

</details>

#### passes when both @export(C) and @repr(C) present

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [make_field("x", make_i32_type())]
val cls = make_exported_class("GoodLayout", fields, true)
val warnings = check_sffi003_repr_required(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### SFFI004 - bitfield width

#### passes for valid explicit @bits metadata

- make bits field
- make bits field
- make bits field
- make bits field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_bits_field("mode", make_u8_type(), 4),
    make_bits_field("output", make_bool_type(), 1),
    make_bits_field("input", make_bool_type(), 1),
    make_bits_field("speed", make_u8_type(), 2)
]
val cls = make_exported_class("GpioRegister", fields, true)
val warnings = check_sffi004_bitfield_width(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### errors when explicit @bits width exceeds the field capacity

- make bits field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI004`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_bits_field("mode", make_u8_type(), 9)
]
val cls = make_exported_class("BadBits", fields, true)
val warnings = check_sffi004_bitfield_width(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI004")
expect(warnings[0].message).to_contain("@bits(9)")
```

</details>

#### errors on 4+ consecutive sub-word fields without @bits

- make field
- make field
- make field
- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI004`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("mode", make_u8_type()),
    make_field("output", make_u8_type()),
    make_field("input", make_u8_type()),
    make_field("speed", make_u8_type())
]
val cls = make_exported_class("GpioRegister", fields, true)
val warnings = check_sffi004_bitfield_width(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI004")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("bitfield")
```

</details>

#### no error for fewer than 4 consecutive sub-word fields

- make field
- make field
- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("a", make_u8_type()),
    make_field("b", make_u8_type()),
    make_field("c", make_i32_type())
]
val cls = make_exported_class("SmallStruct", fields, true)
val warnings = check_sffi004_bitfield_width(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### uses custom primitive capacity for explicit @bits

- make bits field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags_type = make_custom_primitive_i64_type("SffiFlags", 9002)
val fields = [
    make_bits_field("flags", flags_type, 32)
]
val cls = make_exported_class("FlagRegister", fields, true)
val warnings = check_sffi004_bitfield_width(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### SFFI005 - platform-dependent types

#### errors on reference types in exported class without @platform

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI005`
   - Expected: warnings[0].severity equals `ERROR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("data_ref", make_ref_type())
]
val cls = make_exported_class("RefHolder", fields, true)
val warnings = check_sffi005_platform_dependent(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI005")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("reference")
```

</details>

#### keeps platform-tagged reference layout as warning

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI005`
   - Expected: warnings[0].severity equals `WARNING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("data_ref", make_ref_type())
]
val cls = make_exported_platform_class("RefHolder", fields, true, make_platform_default())
val warnings = check_sffi005_platform_dependent(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI005")
expect(warnings[0].severity).to_equal("WARNING")
expect(warnings[0].hint).to_contain("@platform")
```

</details>

#### surfaces @platform missing explicit layout hint as warning

- make field
   - Expected: warnings.len() equals `1`
   - Expected: warnings[0].code equals `SFFI008`
   - Expected: warnings[0].severity equals `WARNING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("data_ref", make_ref_type())
]
val cls = make_exported_platform_class("RefHolder", fields, true, make_platform_missing_hint())
val warnings = check_sffi008_platform_attr_diagnostics(cls, "test.spl")
expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI008")
expect(warnings[0].severity).to_equal("WARNING")
expect(warnings[0].message).to_contain("@platform")
```

</details>

#### no warning for fixed-size types

- make field
- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_f64_type())
]
val cls = make_exported_class("FixedSize", fields, true)
val warnings = check_sffi005_platform_dependent(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### lint_sffi_export - main entry

#### returns empty list for non-exported class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [make_field("data", make_dict_type())]
val cls = make_non_exported_class("Internal", fields)
val warnings = lint_sffi_export(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### collects warnings from all checks on exported class

- make field
- make field


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("name", make_str_type()),
    make_field("items", make_array_type())
]
# Without @repr("C") to also trigger SFFI003
val cls = make_exported_class("MultiWarn", fields, false)
val warnings = lint_sffi_export(cls, "test.spl")
# Should have: SFFI001 (array), SFFI002 (text), SFFI003 (no repr)
val sffi001 = find_by_code(warnings, "SFFI001")
val sffi002 = find_by_code(warnings, "SFFI002")
val sffi003 = find_by_code(warnings, "SFFI003")
expect(sffi001.len()).to_be_greater_than(0)
expect(sffi002.len()).to_be_greater_than(0)
expect(sffi003.len()).to_be_greater_than(0)
```

</details>

#### clean class passes all checks

- make field
- make field
   - Expected: warnings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = [
    make_field("x", make_i32_type()),
    make_field("y", make_f64_type())
]
val cls = make_exported_class("CleanClass", fields, true)
val warnings = lint_sffi_export(cls, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [SFFI bidirectional class interop — layout safety](SFFI bidirectional class interop — layout safety)
- **Plan:** [parsed-questing-goose.md](parsed-questing-goose.md)
- **Design:** [sffi_external_library_pattern.md](sffi_external_library_pattern.md)


</details>
