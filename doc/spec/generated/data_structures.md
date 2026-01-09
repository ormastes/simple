# Simple Language Data Structures - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/data_structures_spec.spl`
> **Generated:** 2026-01-09 06:15:42
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/data_structures_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** data_structures.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (32 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from data_structures.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/data_structures.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `APIs` | [19](#visibility_and_access_19) |
| `Access` | [19](#visibility_and_access_19) |
| `Active` | [14](#strong_enums_14) |
| `Added` | [14](#strong_enums_14) |
| `Algebraic` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Alice` | [3](#classes_reference_types_3), [5](#classes_reference_types_5), [6](#auto_forwarding_properties_getsetis_6) |
| `Always` | [32](#bitfields_32) |
| `And` | [19](#visibility_and_access_19) |
| `Arithmetic` | [30](#bitfields_30) |
| `Associated` | [11](#enums_algebraic_data_types_11) |
| `Auto` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `AutoForwardingPropertiesGetsetis` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `BUG` | [14](#strong_enums_14) |
| `Bad` | [13](#strong_enums_13) |
| `BadRequest` | [13](#strong_enums_13) |
| `Bitfields` | [24](#bitfields_24), [25](#bitfields_25), [26](#bitfields_26), [27](#bitfields_27), [28](#bitfields_28), ... (9 total) |
| `Blue` | [12](#enums_algebraic_data_types_12) |
| `CORRECT` | [18](#option_type_18) |
| `Circle` | [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Clamp` | [31](#bitfields_31) |
| `ClampTest` | [32](#bitfields_32) |
| `Classes` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `ClassesReferenceTypes` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `Clear` | [25](#bitfields_25) |
| `Click` | [15](#strong_enums_15) |
| `Clone` | [12](#enums_algebraic_data_types_12) |
| `Color` | [4](#classes_reference_types_4), [12](#enums_algebraic_data_types_12), [26](#bitfields_26) |
| `Combined` | [29](#bitfields_29) |
| `Common` | [12](#enums_algebraic_data_types_12) |
| `Compact` | [31](#bitfields_31) |
| `Compile` | [18](#option_type_18) |
| `Config` | [21](#read_config) |
| `Counter` | [7](#auto_forwarding_properties_getsetis_7) |
| `Cursor` | [2](#structs_value_types_2) |
| `Data` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Debug` | [12](#enums_algebraic_data_types_12), [32](#bitfields_32) |
| `Drawable` | [12](#enums_algebraic_data_types_12) |
| `ERROR` | [14](#strong_enums_14), [18](#option_type_18), [30](#bitfields_30) |
| `Enums` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12), [13](#strong_enums_13), [14](#strong_enums_14), ... (6 total) |
| `EnumsAlgebraicDataTypes` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Equivalent` | [21](#read_config) |
| `Err` | [9](#enums_algebraic_data_types_9), [10](#handle), [20](#result_type_20), [21](#read_config), [22](#result_type_22) |
| `Error` | [1](#structs_value_types_1), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8), [10](#handle), [23](#result_type_23) |
| `Event` | [15](#strong_enums_15) |
| `Example` | [16](#example) |
| `Explicit` | [18](#option_type_18), [29](#bitfields_29), [31](#bitfields_31) |
| `FULL` | [27](#bitfields_27) |
| `Fields` | [4](#classes_reference_types_4) |
| `Flags` | [24](#bitfields_24), [25](#bitfields_25) |
| `Forwarding` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `Get` | [25](#bitfields_25) |
| `Gets` | [6](#auto_forwarding_properties_getsetis_6) |
| `Getsetis` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `Green` | [12](#enums_algebraic_data_types_12) |
| `Handle` | [10](#handle) |
| `HttpStatus` | [13](#strong_enums_13) |
| `Implicit` | [18](#option_type_18) |
| `Inactive` | [14](#strong_enums_14) |
| `Integer` | [16](#example) |
| `Internal` | [7](#auto_forwarding_properties_getsetis_7) |
| `Invalid` | [20](#result_type_20) |
| `IoError` | [21](#read_config) |
| `Literals` | [28](#bitfields_28) |
| `MotorControl` | [29](#bitfields_29) |
| `Not` | [13](#strong_enums_13) |
| `NotFound` | [13](#strong_enums_13) |
| `Option` | [17](#option_type_17), [18](#option_type_18) |
| `OptionType` | [17](#option_type_17), [18](#option_type_18) |
| `Panics` | [22](#result_type_22) |
| `ParseError` | [20](#result_type_20) |
| `Pending` | [14](#strong_enums_14) |
| `Permission` | [27](#bitfields_27) |
| `Person` | [3](#classes_reference_types_3), [5](#classes_reference_types_5), [6](#auto_forwarding_properties_getsetis_6) |
| `Point` | [1](#structs_value_types_1) |
| `Position` | [30](#bitfields_30) |
| `Private` | [19](#visibility_and_access_19) |
| `Properties` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `Public` | [19](#visibility_and_access_19) |
| `Range` | [29](#bitfields_29) |
| `Read` | [21](#read_config) |
| `ReadConfig` | [21](#read_config) |
| `Rectangle` | [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Red` | [12](#enums_algebraic_data_types_12) |
| `Reference` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `Release` | [32](#bitfields_32) |
| `Result` | [9](#enums_algebraic_data_types_9), [10](#handle), [20](#result_type_20), [21](#read_config), [22](#result_type_22), ... (7 total) |
| `ResultType` | [20](#result_type_20), [22](#result_type_22), [23](#result_type_23) |
| `Returns` | [21](#read_config) |
| `RobotArm` | [28](#bitfields_28) |
| `SafeTest` | [32](#bitfields_32) |
| `SecureData` | [8](#auto_forwarding_properties_getsetis_8) |
| `SensorData` | [29](#bitfields_29) |
| `Server` | [13](#strong_enums_13) |
| `ServerError` | [13](#strong_enums_13) |
| `Sets` | [6](#auto_forwarding_properties_getsetis_6) |
| `Shape` | [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `Silently` | [14](#strong_enums_14) |
| `Status` | [14](#strong_enums_14) |
| `String` | [3](#classes_reference_types_3), [9](#enums_algebraic_data_types_9), [16](#example) |
| `Strong` | [13](#strong_enums_13), [14](#strong_enums_14), [15](#strong_enums_15) |
| `StrongEnums` | [13](#strong_enums_13), [14](#strong_enums_14), [15](#strong_enums_15) |
| `Structs` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `StructsValueTypes` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `Success` | [10](#handle), [13](#strong_enums_13) |
| `Test` | [32](#bitfields_32) |
| `These` | [6](#auto_forwarding_properties_getsetis_6), [23](#result_type_23) |
| `Type` | [17](#option_type_17), [18](#option_type_18), [20](#result_type_20), [22](#result_type_22), [23](#result_type_23) |
| `Types` | [1](#structs_value_types_1), [2](#structs_value_types_2), [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5), ... (8 total) |
| `Unauthorized` | [13](#strong_enums_13) |
| `Usage` | [11](#enums_algebraic_data_types_11) |
| `User` | [17](#option_type_17), [18](#option_type_18), [19](#visibility_and_access_19) |
| `UserId` | [17](#option_type_17), [18](#option_type_18), [19](#visibility_and_access_19) |
| `UserStatus` | [19](#visibility_and_access_19) |
| `Uses` | [19](#visibility_and_access_19) |
| `Value` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `Visibility` | [19](#visibility_and_access_19) |
| `VisibilityAndAccess` | [19](#visibility_and_access_19) |
| `Wide` | [31](#bitfields_31) |
| `With` | [14](#strong_enums_14) |
| `Without` | [14](#strong_enums_14) |
| `access` | [19](#visibility_and_access_19) |
| `activate` | [14](#strong_enums_14) |
| `algebraic` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `allow` | [15](#strong_enums_15) |
| `and` | [19](#visibility_and_access_19) |
| `area` | [11](#enums_algebraic_data_types_11) |
| `arithmetic` | [29](#bitfields_29) |
| `assert_compiles` | [1](#structs_value_types_1), [2](#structs_value_types_2), [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5), ... (29 total) |
| `auto` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `auto_forwarding_properties_getsetis` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `birthday` | [3](#classes_reference_types_3) |
| `bitfields` | [24](#bitfields_24), [25](#bitfields_25), [26](#bitfields_26), [27](#bitfields_27), [28](#bitfields_28), ... (9 total) |
| `classes` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `classes_reference_types` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `config` | [21](#read_config) |
| `data` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `deactivate` | [14](#strong_enums_14) |
| `degrees` | [28](#bitfields_28) |
| `derive` | [12](#enums_algebraic_data_types_12) |
| `draw` | [12](#enums_algebraic_data_types_12) |
| `draw_circle` | [12](#enums_algebraic_data_types_12) |
| `draw_rect` | [12](#enums_algebraic_data_types_12) |
| `enums` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12), [13](#strong_enums_13), [14](#strong_enums_14), ... (6 total) |
| `enums_algebraic_data_types` | [9](#enums_algebraic_data_types_9), [11](#enums_algebraic_data_types_11), [12](#enums_algebraic_data_types_12) |
| `example` | [16](#example) |
| `find` | [17](#option_type_17) |
| `find_user` | [18](#option_type_18) |
| `foo` | [23](#result_type_23) |
| `forwarding` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `function` | [11](#enums_algebraic_data_types_11) |
| `get_count` | [7](#auto_forwarding_properties_getsetis_7) |
| `get_name` | [6](#auto_forwarding_properties_getsetis_6) |
| `get_password` | [8](#auto_forwarding_properties_getsetis_8) |
| `getsetis` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `handle` | [10](#handle) |
| `handle_some` | [15](#strong_enums_15) |
| `handle_status` | [13](#strong_enums_13) |
| `hash` | [8](#auto_forwarding_properties_getsetis_8), [19](#visibility_and_access_19) |
| `increment` | [7](#auto_forwarding_properties_getsetis_7) |
| `is_active` | [6](#auto_forwarding_properties_getsetis_6) |
| `is_err` | [22](#result_type_22) |
| `is_numeric` | [20](#result_type_20) |
| `is_ok` | [22](#result_type_22) |
| `lookup` | [17](#option_type_17) |
| `narrow` | [31](#bitfields_31) |
| `narrowing` | [31](#bitfields_31) |
| `on_click` | [15](#strong_enums_15) |
| `option` | [17](#option_type_17), [18](#option_type_18) |
| `option_type` | [17](#option_type_17), [18](#option_type_18) |
| `panic` | [32](#bitfields_32) |
| `parse_int` | [20](#result_type_20) |
| `parse_toml` | [21](#read_config) |
| `percentage` | [28](#bitfields_28) |
| `process` | [14](#strong_enums_14) |
| `properties` | [6](#auto_forwarding_properties_getsetis_6), [7](#auto_forwarding_properties_getsetis_7), [8](#auto_forwarding_properties_getsetis_8) |
| `raw` | [25](#bitfields_25) |
| `read` | [21](#read_config) |
| `read_config` | [21](#read_config) |
| `read_config_verbose` | [21](#read_config) |
| `read_file` | [21](#read_config) |
| `reference` | [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5) |
| `result` | [20](#result_type_20), [22](#result_type_22), [23](#result_type_23) |
| `result_type` | [20](#result_type_20), [22](#result_type_22), [23](#result_type_23) |
| `saturate` | [31](#bitfields_31) |
| `scale` | [11](#enums_algebraic_data_types_11) |
| `set_count` | [7](#auto_forwarding_properties_getsetis_7) |
| `set_name` | [6](#auto_forwarding_properties_getsetis_6) |
| `set_password` | [8](#auto_forwarding_properties_getsetis_8) |
| `strong` | [13](#strong_enums_13), [14](#strong_enums_14), [15](#strong_enums_15) |
| `strong_enums` | [13](#strong_enums_13), [14](#strong_enums_14), [15](#strong_enums_15) |
| `structs` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `structs_value_types` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `to_int` | [20](#result_type_20) |
| `type` | [17](#option_type_17), [18](#option_type_18), [20](#result_type_20), [22](#result_type_22), [23](#result_type_23) |
| `types` | [1](#structs_value_types_1), [2](#structs_value_types_2), [3](#classes_reference_types_3), [4](#classes_reference_types_4), [5](#classes_reference_types_5), ... (8 total) |
| `unit_circle` | [11](#enums_algebraic_data_types_11) |
| `unwrap` | [22](#result_type_22) |
| `unwrap_err` | [22](#result_type_22) |
| `unwrap_or` | [22](#result_type_22) |
| `value` | [1](#structs_value_types_1), [2](#structs_value_types_2) |
| `verify` | [8](#auto_forwarding_properties_getsetis_8), [19](#visibility_and_access_19) |
| `visibility` | [19](#visibility_and_access_19) |
| `visibility_and_access` | [19](#visibility_and_access_19) |
| `widen` | [31](#bitfields_31) |

---

## Test Cases (32 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [structs_value_types_1](#structs_value_types_1) | Structs (Value Types) | `Types`, `Value`, `structs_value_types` +8 |
| 2 | [structs_value_types_2](#structs_value_types_2) | Structs (Value Types) | `Types`, `Value`, `structs_value_types` +7 |
| 3 | [classes_reference_types_3](#classes_reference_types_3) | Classes (Reference Types) | `Types`, `ClassesReferenceTypes`, `classes` +10 |
| 4 | [classes_reference_types_4](#classes_reference_types_4) | Classes (Reference Types) | `Types`, `ClassesReferenceTypes`, `classes` +8 |
| 5 | [classes_reference_types_5](#classes_reference_types_5) | Classes (Reference Types) | `Types`, `ClassesReferenceTypes`, `classes` +8 |
| 6 | [auto_forwarding_properties_getsetis_6](#auto_forwarding_properties_getsetis_6) | Auto-Forwarding Properties (get/set/is) | `AutoForwardingPropertiesGetsetis`, `Forwarding`, `auto_forwarding_properties_getsetis` +16 |
| 7 | [auto_forwarding_properties_getsetis_7](#auto_forwarding_properties_getsetis_7) | Auto-Forwarding Properties (get/set/is) | `AutoForwardingPropertiesGetsetis`, `Forwarding`, `auto_forwarding_properties_getsetis` +14 |
| 8 | [auto_forwarding_properties_getsetis_8](#auto_forwarding_properties_getsetis_8) | Auto-Forwarding Properties (get/set/is) | `AutoForwardingPropertiesGetsetis`, `Forwarding`, `auto_forwarding_properties_getsetis` +14 |
| 9 | [enums_algebraic_data_types_9](#enums_algebraic_data_types_9) | Enums (Algebraic Data Types) | `Enums`, `enums_algebraic_data_types`, `Algebraic` +11 |
| 10 | [handle](#handle) | Enums (Algebraic Data Types) | `Handle`, `handle`, `Success` +3 |
| 11 | [enums_algebraic_data_types_11](#enums_algebraic_data_types_11) | Enums (Algebraic Data Types) | `Enums`, `enums_algebraic_data_types`, `Algebraic` +17 |
| 12 | [enums_algebraic_data_types_12](#enums_algebraic_data_types_12) | Enums (Algebraic Data Types) | `Enums`, `enums_algebraic_data_types`, `Algebraic` +23 |
| 13 | [strong_enums_13](#strong_enums_13) | Strong Enums | `Enums`, `StrongEnums`, `enums` +14 |
| 14 | [strong_enums_14](#strong_enums_14) | Strong Enums | `Enums`, `StrongEnums`, `enums` +17 |
| 15 | [strong_enums_15](#strong_enums_15) | Strong Enums | `Enums`, `StrongEnums`, `enums` +9 |
| 16 | [example](#example) | Union Types | `example`, `Example`, `String` +1 |
| 17 | [option_type_17](#option_type_17) | Option Type | `option`, `OptionType`, `Type` +8 |
| 18 | [option_type_18](#option_type_18) | Option Type | `option`, `OptionType`, `Type` +12 |
| 19 | [visibility_and_access_19](#visibility_and_access_19) | Visibility and Access | `VisibilityAndAccess`, `visibility`, `and` +15 |
| 20 | [result_type_20](#result_type_20) | Result Type | `Type`, `type`, `result` +10 |
| 21 | [read_config](#read_config) | Result Type | `read_config`, `read`, `ReadConfig` +11 |
| 22 | [result_type_22](#result_type_22) | Result Type | `Type`, `type`, `result` +11 |
| 23 | [result_type_23](#result_type_23) | Result Type | `Type`, `type`, `result` +7 |
| 24 | [bitfields_24](#bitfields_24) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +1 |
| 25 | [bitfields_25](#bitfields_25) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +4 |
| 26 | [bitfields_26](#bitfields_26) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +1 |
| 27 | [bitfields_27](#bitfields_27) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +2 |
| 28 | [bitfields_28](#bitfields_28) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +4 |
| 29 | [bitfields_29](#bitfields_29) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +6 |
| 30 | [bitfields_30](#bitfields_30) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +4 |
| 31 | [bitfields_31](#bitfields_31) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +8 |
| 32 | [bitfields_32](#bitfields_32) | Bitfields | `Bitfields`, `bitfields`, `assert_compiles` +7 |

---

### Test 1: Structs (Value Types) {#structs_value_types_1}

*Source line: ~7*

**Test name:** `structs_value_types_1`

**Description:**

Structs are value types (similar to structs in C or Rust). They are copied on assignment and passed ...

**Linked Symbols:**
- `Types`
- `Value`
- `structs_value_types`
- `value`
- `types`
- `Structs`
- `StructsValueTypes`
- `structs`
- `assert_compiles`
- `Point`
- ... and 1 more

**Code:**

```simple
test "structs_value_types_1":
    struct Point:
        x: f64
        y: f64

    a = Point(x: 1, y: 2)
    b = a              # copies the values x=1, y=2 into b
    # a.x = 5          # Error: Point is immutable by default
    assert_compiles()
```

### Test 2: Structs (Value Types) {#structs_value_types_2}

*Source line: ~21*

**Test name:** `structs_value_types_2`

**Description:**

Unless marked `mut`, a struct's fields cannot be changed after construction:

**Linked Symbols:**
- `Types`
- `Value`
- `structs_value_types`
- `value`
- `types`
- `Structs`
- `StructsValueTypes`
- `structs`
- `assert_compiles`
- `Cursor`

**Code:**

```simple
test "structs_value_types_2":
    mut struct Cursor:
        x: f64
        y: f64

    let c = Cursor(x: 0, y: 0)
    c.x = 10           # OK: Cursor is mutable
    assert_compiles()
```

### Test 3: Classes (Reference Types) {#classes_reference_types_3}

*Source line: ~7*

**Test name:** `classes_reference_types_3`

**Description:**

Classes are reference types, allocated on the heap and managed by the runtime (with garbage collecti...

**Linked Symbols:**
- `Types`
- `ClassesReferenceTypes`
- `classes`
- `Reference`
- `reference`
- `Classes`
- `types`
- `classes_reference_types`
- `assert_compiles`
- `String`
- ... and 3 more

**Code:**

```simple
test "classes_reference_types_3":
    class Person:
        name: String
        age: i32

        fn birthday():
            self.age = self.age + 1

    let p = Person(name: "Alice", age: 30)
    p.birthday()          # now age is 31
    assert_compiles()
```

### Test 4: Classes (Reference Types) {#classes_reference_types_4}

*Source line: ~23*

**Test name:** `classes_reference_types_4`

**Description:**

By default, class instances are mutable. Use `immut` for immutable classes:

**Linked Symbols:**
- `Types`
- `ClassesReferenceTypes`
- `classes`
- `Reference`
- `reference`
- `Classes`
- `types`
- `classes_reference_types`
- `assert_compiles`
- `Color`
- ... and 1 more

**Code:**

```simple
test "classes_reference_types_4":
    immut class Color:
        red: u8
        green: u8
        blue: u8

    # Fields cannot be changed after construction
    assert_compiles()
```

### Test 5: Classes (Reference Types) {#classes_reference_types_5}

*Source line: ~42*

**Test name:** `classes_reference_types_5`

**Description:**

- Mutable by default - Use `immut class` for immutable classes
- Reference equality by default - Ove...

**Linked Symbols:**
- `Types`
- `ClassesReferenceTypes`
- `classes`
- `Reference`
- `reference`
- `Classes`
- `types`
- `classes_reference_types`
- `assert_compiles`
- `Person`
- ... and 1 more

**Code:**

```simple
test "classes_reference_types_5":
    let p = Person(name: "Alice", age: 30)
    let q = p              # q and p refer to the same object
    q.age = 31             # p.age is also 31
    assert_compiles()
```

### Test 6: Auto-Forwarding Properties (get/set/is) {#auto_forwarding_properties_getsetis_6}

*Source line: ~7*

**Test name:** `auto_forwarding_properties_getsetis_6`

**Description:**

Simple provides automatic property forwarding for methods prefixed with `get_`, `set_`, or `is_`. Th...

**Linked Symbols:**
- `AutoForwardingPropertiesGetsetis`
- `Forwarding`
- `auto_forwarding_properties_getsetis`
- `Auto`
- `Getsetis`
- `properties`
- `Properties`
- `auto`
- `forwarding`
- `getsetis`
- ... and 9 more

**Code:**

```simple
test "auto_forwarding_properties_getsetis_6":
    class Person:
        # These methods auto-create private backing field '_name'
        fn get_name() -> str:
            return _name

        fn set_name(value: str):
            _name = value

        # 'is_' prefix for boolean properties
        fn is_active() -> bool:
            return _active

    let p = Person()
    p.set_name("Alice")      # Sets _name
    print p.get_name()       # Gets _name -> "Alice"
    assert_compiles()
```

### Test 7: Auto-Forwarding Properties (get/set/is) {#auto_forwarding_properties_getsetis_7}

*Source line: ~37*

**Test name:** `auto_forwarding_properties_getsetis_7`

**Description:**

If only `get_` is defined, the property is read-only from outside:

**Linked Symbols:**
- `AutoForwardingPropertiesGetsetis`
- `Forwarding`
- `auto_forwarding_properties_getsetis`
- `Auto`
- `Getsetis`
- `properties`
- `Properties`
- `auto`
- `forwarding`
- `getsetis`
- ... and 7 more

**Code:**

```simple
test "auto_forwarding_properties_getsetis_7":
    class Counter:
        fn get_count() -> i64:
            return _count

        fn increment():
            _count = _count + 1  # Internal modification OK

    let c = Counter()
    c.increment()
    print c.get_count()  # OK: 1
    # c.set_count(100)   # Error: no setter defined
    assert_compiles()
```

### Test 8: Auto-Forwarding Properties (get/set/is) {#auto_forwarding_properties_getsetis_8}

*Source line: ~55*

**Test name:** `auto_forwarding_properties_getsetis_8`

**Description:**

If only `set_` is defined, the property is write-only from outside:

**Linked Symbols:**
- `AutoForwardingPropertiesGetsetis`
- `Forwarding`
- `auto_forwarding_properties_getsetis`
- `Auto`
- `Getsetis`
- `properties`
- `Properties`
- `auto`
- `forwarding`
- `getsetis`
- ... and 7 more

**Code:**

```simple
test "auto_forwarding_properties_getsetis_8":
    class SecureData:
        fn set_password(value: str):
            _password = hash(value)

        fn verify(input: str) -> bool:
            return hash(input) == _password

    let s = SecureData()
    s.set_password("secret123")
    # print s.get_password()  # Error: no getter defined
    assert_compiles()
```

### Test 9: Enums (Algebraic Data Types) {#enums_algebraic_data_types_9}

*Source line: ~7*

**Test name:** `enums_algebraic_data_types_9`

**Description:**

Enums define a type that can be one of several variants, each possibly carrying data. They are algeb...

**Linked Symbols:**
- `Enums`
- `enums_algebraic_data_types`
- `Algebraic`
- `data`
- `Types`
- `enums`
- `Data`
- `EnumsAlgebraicDataTypes`
- `algebraic`
- `types`
- ... and 4 more

**Code:**

```simple
test "enums_algebraic_data_types_9":
    enum Result[T]:
        Ok(value: T)
        Err(error: String)
    assert_compiles()
```

### Test 10: Enums (Algebraic Data Types) {#handle}

*Source line: ~19*

**Test name:** `handle`

**Description:**

Enums are typically used with pattern matching:

**Linked Symbols:**
- `Handle`
- `handle`
- `Success`
- `Err`
- `Result`
- `Error`

**Code:**

```simple
fn handle(result: Result[i64]):
    match result:
        case Ok(val):
            print "Success: {val}"
        case Err(msg):
            print "Error: {msg}"
```

### Test 11: Enums (Algebraic Data Types) {#enums_algebraic_data_types_11}

*Source line: ~39*

**Test name:** `enums_algebraic_data_types_11`

**Description:**

Enums can have methods added via impl blocks:

**Linked Symbols:**
- `Enums`
- `enums_algebraic_data_types`
- `Algebraic`
- `data`
- `Types`
- `enums`
- `Data`
- `EnumsAlgebraicDataTypes`
- `algebraic`
- `types`
- ... and 10 more

**Code:**

```simple
test "enums_algebraic_data_types_11":
    enum Shape:
        Circle(radius: f64)
        Rectangle(width: f64, height: f64)

    impl Shape:
        fn area(self) -> f64:
            match self:
                case Circle(r): return 3.14159 * r * r
                case Rectangle(w, h): return w * h

        fn scale(self, factor: f64) -> Shape:
            match self:
                case Circle(r): return Shape.Circle(radius: r * factor)
                case Rectangle(w, h): return Shape.Rectangle(width: w * factor, height: h * factor)

        # Associated function (no self)
        fn unit_circle() -> Shape:
            return Shape.Circle(radius: 1.0)

    # Usage
    let s = Shape.Circle(radius: 5.0)
    print s.area()           # 78.54
    let s2 = s.scale(2.0)    # Circle with radius 10.0
    assert_compiles()
```

### Test 12: Enums (Algebraic Data Types) {#enums_algebraic_data_types_12}

*Source line: ~67*

**Test name:** `enums_algebraic_data_types_12`

**Description:**

fn scale(self, factor: f64) -> Shape:
        match self:
            case Circle(r): return Shape.C...

**Linked Symbols:**
- `Enums`
- `enums_algebraic_data_types`
- `Algebraic`
- `data`
- `Types`
- `enums`
- `Data`
- `EnumsAlgebraicDataTypes`
- `algebraic`
- `types`
- ... and 16 more

**Code:**

```simple
test "enums_algebraic_data_types_12":
    trait Drawable:
        fn draw(self)

    impl Drawable for Shape:
        fn draw(self):
            match self:
                case Circle(r): draw_circle(r)
                case Rectangle(w, h): draw_rect(w, h)

    # Common traits can be derived
    #[derive(Eq, Clone, Debug)]
    enum Color:
        Red
        Green
        Blue
    assert_compiles()
```

### Test 13: Strong Enums {#strong_enums_13}

*Source line: ~7*

**Test name:** `strong_enums_13`

**Description:**

The `#[strong]` attribute enforces exhaustive explicit matching, disallowing wildcard `_` patterns.

**Linked Symbols:**
- `Enums`
- `StrongEnums`
- `enums`
- `strong`
- `Strong`
- `strong_enums`
- `assert_compiles`
- `HttpStatus`
- `NotFound`
- `Success`
- ... and 7 more

**Code:**

```simple
test "strong_enums_13":
    #[strong]
    enum HttpStatus:
        Ok
        NotFound
        ServerError
        BadRequest
        Unauthorized

    fn handle_status(status: HttpStatus) -> str:
        match status:
            case Ok: "Success"
            case NotFound: "Not found"
            case ServerError: "Server error"
            case BadRequest: "Bad request"
            case Unauthorized: "Unauthorized"
            # No _ allowed - all cases must be explicit
    assert_compiles()
```

### Test 14: Strong Enums {#strong_enums_14}

*Source line: ~30*

**Test name:** `strong_enums_14`

**Description:**

Strong enums prevent bugs when new variants are added:

**Linked Symbols:**
- `Enums`
- `StrongEnums`
- `enums`
- `strong`
- `Strong`
- `strong_enums`
- `activate`
- `assert_compiles`
- `Active`
- `Pending`
- ... and 10 more

**Code:**

```simple
test "strong_enums_14":
    # Without #[strong] - wildcard hides missing cases
    enum Status:
        Active
        Inactive
        Pending      # Added later

    fn process(s: Status):
        match s:
            case Active: activate()
            case Inactive: deactivate()
            case _: pass     # Silently ignores Pending - BUG!

    # With #[strong] - compiler catches missing cases
    #[strong]
    enum Status:
        Active
        Inactive
        Pending

    fn process(s: Status):
        match s:
            case Active: activate()
            case Inactive: deactivate()
            # ERROR: missing case 'Pending', wildcards not allowed
    assert_compiles()
```

### Test 15: Strong Enums {#strong_enums_15}

*Source line: ~70*

**Test name:** `strong_enums_15`

**Description:**

Use `#[allow(wildcard_match)]` to allow wildcards in specific functions:

**Linked Symbols:**
- `Enums`
- `StrongEnums`
- `enums`
- `strong`
- `Strong`
- `strong_enums`
- `assert_compiles`
- `Click`
- `handle_some`
- `Event`
- ... and 2 more

**Code:**

```simple
test "strong_enums_15":
    #[allow(wildcard_match)]
    fn handle_some(e: Event):
        match e:
            case Click: on_click()
            case _: pass     # OK with attribute
    assert_compiles()
```

### Test 16: Union Types {#example}

*Source line: ~7*

**Test name:** `example`

**Description:**

Simple supports union types for cases where a variable might hold one of multiple types.

**Linked Symbols:**
- `example`
- `Example`
- `String`
- `Integer`

**Code:**

```simple
fn example(x: i64 | str):
    match x:
        case i: i64:
            print "Integer: {i}"
        case s: String:
            print "String: {s}"
```

### Test 17: Option Type {#option_type_17}

*Source line: ~5*

**Test name:** `option_type_17`

**Description:**

A common enum representing "something or nothing":

**Linked Symbols:**
- `option`
- `OptionType`
- `Type`
- `option_type`
- `type`
- `Option`
- `assert_compiles`
- `User`
- `find`
- `lookup`
- ... and 1 more

**Code:**

```simple
test "option_type_17":
    enum Option[T]:
        Some(value: T)
        None

    fn find(id: UserId) -> Option[User]:
        match lookup(id):
            case found:
                return Some(found)
            case _:
                return None
    assert_compiles()
```

### Test 18: Option Type {#option_type_18}

*Source line: ~20*

**Test name:** `option_type_18`

**Description:**

Important: Simple requires explicit `Option[T]` for nullable values. Implicit `nil` is a compile err...

**Linked Symbols:**
- `option`
- `OptionType`
- `Type`
- `option_type`
- `type`
- `Option`
- `assert_compiles`
- `Explicit`
- `CORRECT`
- `Compile`
- ... and 5 more

**Code:**

```simple
test "option_type_18":
    # ERROR: Implicit nullable return
    fn find_user(id: UserId) -> User:  # Compile error if function can return nil
        ...

    # CORRECT: Explicit Option
    fn find_user(id: UserId) -> Option[User]:
        ...
    assert_compiles()
```

### Test 19: Visibility and Access {#visibility_and_access_19}

*Source line: ~5*

**Test name:** `visibility_and_access_19`

**Description:**

By default, all struct and class fields are publicly readable but only modifiable according to mutab...

**Linked Symbols:**
- `VisibilityAndAccess`
- `visibility`
- `and`
- `access`
- `Access`
- `Visibility`
- `visibility_and_access`
- `And`
- `assert_compiles`
- `Private`
- ... and 8 more

**Code:**

```simple
test "visibility_and_access_19":
    class User:
        pub id: UserId           # Public field - uses semantic type
        pub name: str            # OK: str is allowed in public APIs
        pub status: UserStatus   # Uses enum instead of bool
        private password: str    # Private field

        fn verify(input: str) -> bool:   # OK: bool in private method
            return hash(input) == self.password
    assert_compiles()
```

### Test 20: Result Type {#result_type_20}

*Source line: ~5*

**Test name:** `result_type_20`

**Description:**

A common enum representing "success or error":

**Linked Symbols:**
- `Type`
- `type`
- `result`
- `ResultType`
- `result_type`
- `Result`
- `assert_compiles`
- `to_int`
- `Err`
- `parse_int`
- ... and 3 more

**Code:**

```simple
test "result_type_20":
    enum Result[T, E]:
        Ok(value: T)
        Err(error: E)

    fn parse_int(s: str) -> Result[i64, ParseError]:
        if s.is_numeric():
            return Ok(s.to_int())
        return Err(ParseError(msg: "Invalid number: {s}"))
    assert_compiles()
```

### Test 21: Result Type {#read_config}

*Source line: ~20*

**Test name:** `read_config`

**Description:**

The `?` operator propagates errors automatically:

**Linked Symbols:**
- `read_config`
- `read`
- `ReadConfig`
- `Read`
- `Config`
- `config`
- `parse_toml`
- `IoError`
- `Returns`
- `Err`
- ... and 4 more

**Code:**

```simple
fn read_config() -> Result[Config, IoError]:
    let content = read_file("config.toml")?  # Returns early if Err
    let parsed = parse_toml(content)?        # Returns early if Err
    return Ok(Config(parsed))

# Equivalent to:
fn read_config_verbose() -> Result[Config, IoError]:
    match read_file("config.toml"):
        case Ok(content):
            match parse_toml(content):
                case Ok(parsed): return Ok(Config(parsed))
                case Err(e): return Err(e)
        case Err(e): return Err(e)
```

### Test 22: Result Type {#result_type_22}

*Source line: ~38*

**Test name:** `result_type_22`

**Description:**

```simple
fn read_config() -> Result[Config, IoError]:
    let content = read_file("config.toml")?  ...

**Linked Symbols:**
- `Type`
- `type`
- `result`
- `ResultType`
- `result_type`
- `Result`
- `unwrap_err`
- `assert_compiles`
- `Panics`
- `unwrap_or`
- ... and 4 more

**Code:**

```simple
test "result_type_22":
    impl Result[T, E]:
        fn is_ok() -> bool
        fn is_err() -> bool
        fn unwrap() -> T                    # Panics if Err
        fn unwrap_or(default: T) -> T
        fn unwrap_err() -> E                # Panics if Ok
        fn map[U](f: fn(T) -> U) -> Result[U, E]
        fn map_err[F](f: fn(E) -> F) -> Result[T, F]
        fn and_then[U](f: fn(T) -> Result[U, E]) -> Result[U, E]
    assert_compiles()
```

### Test 23: Result Type {#result_type_23}

*Source line: ~52*

**Test name:** `result_type_23`

**Description:**

```simple
impl Result[T, E]:
    fn is_ok() -> bool
    fn is_err() -> bool
    fn unwrap() -> T    ...

**Linked Symbols:**
- `Type`
- `type`
- `result`
- `ResultType`
- `result_type`
- `Result`
- `assert_compiles`
- `foo`
- `These`
- `Error`

**Code:**

```simple
test "result_type_23":
    # These are equivalent:
    fn foo() -> Result[i64, Error]
    fn foo() -> i64 | Error
    assert_compiles()
```

### Test 24: Bitfields {#bitfields_24}

*Source line: ~7*

**Test name:** `bitfields_24`

**Description:**

Bitfields allow compact representation of data at the bit level, useful for hardware registers, prot...

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Flags`

**Code:**

```simple
test "bitfields_24":
    bitfield Flags(u8):
        readable: 1      # bit 0
        writable: 1      # bit 1
        executable: 1    # bit 2
        _reserved: 5     # bits 3-7 (padding, not accessible)
    assert_compiles()
```

### Test 25: Bitfields {#bitfields_25}

*Source line: ~19*

**Test name:** `bitfields_25`

**Description:**

The backing type (`u8`, `u16`, `u32`, `u64`) determines the total size.

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `raw`
- `Get`
- `Clear`
- `Flags`

**Code:**

```simple
test "bitfields_25":
    let f = Flags(readable: 1, writable: 1, executable: 0)
    print f.readable     # 1
    f.writable = 0       # Clear write bit
    let raw = f.raw()    # Get underlying u8 value: 0b00000001
    assert_compiles()
```

### Test 26: Bitfields {#bitfields_26}

*Source line: ~30*

**Test name:** `bitfields_26`

**Description:**

Fields can span multiple bits:

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Color`

**Code:**

```simple
test "bitfields_26":
    bitfield Color(u32):
        red: 8           # bits 0-7
        green: 8         # bits 8-15
        blue: 8          # bits 16-23
        alpha: 8         # bits 24-31

    let c = Color(red: 255, green: 128, blue: 64, alpha: 255)
    assert_compiles()
```

### Test 27: Bitfields {#bitfields_27}

*Source line: ~51*

**Test name:** `bitfields_27`

**Description:**

| Property | Description |
|----------|-------------|
| Packed | Fields are tightly packed with no p...

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Permission`
- `FULL`

**Code:**

```simple
test "bitfields_27":
    bitfield Permission(u8):
        read: 1
        write: 1
        execute: 1

        const READ_ONLY = Permission(read: 1, write: 0, execute: 0)
        const READ_WRITE = Permission(read: 1, write: 1, execute: 0)
        const FULL = Permission(read: 1, write: 1, execute: 1)
    assert_compiles()
```

### Test 28: Bitfields {#bitfields_28}

*Source line: ~70*

**Test name:** `bitfields_28`

**Description:**

Use `suffix:repr` for simple bit-width specification. In type positions, use bare unit suffix (no un...

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `RobotArm`
- `Literals`
- `percentage`
- `degrees`

**Code:**

```simple
test "bitfields_28":
    bitfield RobotArm:
        x: cm:i12           # 12-bit signed centimeters
        y: cm:i12           # 12-bit signed centimeters
        z: cm:u10           # 10-bit unsigned centimeters
        angle: deg:u9       # 9-bit unsigned degrees (0-511)
        grip: pct:u7        # 7-bit percentage (0-100)

    # Literals still use underscore prefix
    let arm = RobotArm(x: 100_cm, y: -50_cm, z: 200_cm, angle: 180_deg, grip: 75_pct)
    print arm.x              # 100_cm (typed value, not raw bits)
    print arm.angle          # 180_deg
    assert_compiles()
```

### Test 29: Bitfields {#bitfields_29}

*Source line: ~88*

**Test name:** `bitfields_29`

**Description:**

Use `where` for range inference, overflow behavior, and debug checking:

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `arithmetic`
- `Explicit`
- `MotorControl`
- `Range`
- `SensorData`
- `Combined`

**Code:**

```simple
test "bitfields_29":
    bitfield SensorData:
        # Range inference - compiler calculates minimum bits
        temp: celsius where range: -40..125            # infers i8
        humidity: pct where range: 0..100              # infers u7

        # Explicit repr + overflow behavior
        pressure: hpa:u16 where checked                # panic on overflow
        altitude: m:i16 where saturate                 # clamp to min/max
        heading: deg:u9 where wrap                     # modular arithmetic (0-511)

    bitfield MotorControl:
        # Combined constraints
        position: cm where range: -1000..1000, checked     # i11, debug-checked
        velocity: mps:u8 where saturate                    # clamp to 0-255
        torque: nm where range: 0..100, default: 0_nm      # with default value
    assert_compiles()
```

### Test 30: Bitfields {#bitfields_30}

*Source line: ~146*

**Test name:** `bitfields_30`

**Description:**

Unit-typed bitfield fields maintain full type safety:

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Position`
- `ERROR`
- `Arithmetic`
- `Result`

**Code:**

```simple
test "bitfields_30":
    bitfield Position:
        x: cm:i12
        y: cm:i12

    let pos = Position(x: 100_cm, y: 200_cm)
    # pos.x = 50_m      # ERROR: cannot assign m to cm field
    # pos.x = 50        # ERROR: cannot assign bare integer to cm field
    pos.x = 50_cm       # OK: same unit type

    # Arithmetic preserves unit type
    let new_x = pos.x + 10_cm    # Result: cm:i12
    assert_compiles()
```

### Test 31: Bitfields {#bitfields_31}

*Source line: ~162*

**Test name:** `bitfields_31`

**Description:**

let pos = Position(x: 100_cm, y: 200_cm)
# pos.x = 50_m      # ERROR: cannot assign m to cm field
# ...

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Compact`
- `Explicit`
- `Wide`
- `widen`
- `Clamp`
- `narrow`
- `saturate`
- ... and 1 more

**Code:**

```simple
test "bitfields_31":
    bitfield Compact:
        dist: cm:u8

    bitfield Wide:
        dist: cm:u16

    let c = Compact(dist: 100_cm)
    let w = Wide(dist: c.dist.widen())    # Explicit widening
    # let w2 = Wide(dist: c.dist)         # OK: implicit widening allowed

    let c2 = Compact(dist: w.dist.narrow())   # Explicit narrowing (checked)
    let c3 = Compact(dist: w.dist.saturate()) # Clamp to 0-255
    assert_compiles()
```

### Test 32: Bitfields {#bitfields_32}

*Source line: ~181*

**Test name:** `bitfields_32`

**Description:**

In debug builds, assignments to bit-limited fields are checked:

**Linked Symbols:**
- `Bitfields`
- `bitfields`
- `assert_compiles`
- `Test`
- `SafeTest`
- `panic`
- `Debug`
- `Release`
- `Always`
- `ClampTest`

**Code:**

```simple
test "bitfields_32":
    bitfield Test:
        value: cm:u8              # 0-255 range

    let t = Test(value: 255_cm)   # OK
    # t.value = 256_cm            # Debug: panic! Release: undefined behavior

    bitfield SafeTest:
        value: cm:u8 where checked    # Always checked

    let s = SafeTest(value: 255_cm)
    # s.value = 256_cm            # Always panic (debug and release)

    bitfield ClampTest:
        value: cm:u8 where saturate

    let cl = ClampTest(value: 300_cm)
    print cl.value                # 255_cm (clamped)
    assert_compiles()
```

---

## Source Code

**View full specification:** [data_structures_spec.spl](../../tests/specs/data_structures_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/data_structures_spec.spl`*
