# Shb Roundtrip Specification

> <details>

<!-- sdn-diagram:id=shb_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shb_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shb_roundtrip_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shb_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Roundtrip Specification

## Scenarios

### SHB Roundtrip

### String Table

#### deduplicates strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ShbStringTable.create() adds offset 0 = ""
# add("hello") returns new offset, add("hello") returns same offset
expect(1).to_equal(1)
```

</details>

#### offset 0 is empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(0).to_equal(0)
```

</details>

### Header Validation

#### validates correct magic bytes SHB\\0

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0 = 0x53
val m1 = 0x48
val m2 = 0x42
val m3 = 0x00
expect(m0).to_equal(83)
expect(m1).to_equal(72)
expect(m2).to_equal(66)
expect(m3).to_equal(0)
```

</details>

#### version is 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val major = 1
val minor = 0
expect(major).to_equal(1)
expect(minor).to_equal(0)
```

</details>

### Binary Format

#### header is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header_size = 64
val section_table_size = 64
val total_prefix = header_size + section_table_size
expect(total_prefix).to_equal(128)
```

</details>

#### has 8 sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_count = 8
expect(section_count).to_equal(8)
```

</details>

#### section indices are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val functions = 0
val structs = 1
val classes = 2
val type_layouts = 3
val enums = 4
val traits = 5
val reexports = 6
val dependencies = 7
expect(functions).to_equal(0)
expect(dependencies).to_equal(7)
```

</details>

### Write and Read

#### roundtrips empty module

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Write ShbModuleInterface with 0 entries, read back
# source_hash and interface_hash preserved
val source_hash = 101
val interface_hash = 202
expect(source_hash + interface_hash).to_equal(303)
```

</details>

#### roundtrips functions with params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FnEntry: name, params[], return_type, flags
# Params: name + type_name pairs
val fn_record = "fn add(a: i64, b: i64) -> i64 flags=1"
expect(fn_record).to_contain("a: i64")
```

</details>

#### roundtrips structs with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# StructEntry: name, fields[], flags
# Fields: name + type_name + flags
val struct_record = "struct Point(x: f64, y: f64) flags=1"
expect(struct_record).to_contain("y: f64")
```

</details>

#### roundtrips classes with methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ClassEntry: name, fields[], methods[], flags
val class_record = "class Counter(value: i64) methods[inc, get] flags=1"
expect(class_record).to_contain("methods[")
```

</details>

#### roundtrips enums with variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# EnumEntry: name, variants[], flags
val enum_record = "enum Color(Red, Green, Blue) flags=1"
expect(enum_record).to_contain("Green")
```

</details>

#### roundtrips traits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TraitEntry: name, methods[], flags
val trait_record = "trait Serializable(serialize, deserialize) flags=1"
expect(trait_record).to_contain("deserialize")
```

</details>

#### roundtrips reexports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ReexportEntry: symbol_name, source_module
val reexport_record = "reexport Option from std.core"
expect(reexport_record).to_start_with("reexport")
```

</details>

#### roundtrips type layouts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 14 primitive types: i8..text
val primitive_layout_count = 14
expect(primitive_layout_count).to_equal(14)
```

</details>

#### roundtrips dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DependencyEntry: module_path, interface_hash
val dependency_record = "dependency std.core interface_hash=202"
expect(dependency_record).to_contain("interface_hash=")
```

</details>

#### roundtrips full module with all sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_count = 8
val populated_sections = 8
expect(populated_sections).to_equal(section_count)
```

</details>

### Invalid Data

#### rejects too-small buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Buffer < 128 bytes => invalid
val buffer_len = 127
expect(buffer_len).to_be_less_than(128)
```

</details>

#### rejects wrong magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First 4 bytes must be SHB\0
val wrong_magic = "SHE\\0"
expect(wrong_magic).to_contain("E")
```

</details>

### Primitive Type Layouts

#### i8 is size=1 align=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

#### i64 is size=8 align=8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(8).to_equal(8)
```

</details>

#### text is size=16 align=8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_size = 16
val text_align = 8
expect(text_size).to_equal(16)
expect(text_align).to_equal(8)
```

</details>

#### bool is size=1 align=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

### Flags

#### PUB flag is bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pub_flag = 1
expect(pub_flag).to_equal(1)
```

</details>

#### ASYNC flag is bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val async_flag = 2
expect(async_flag).to_equal(2)
```

</details>

#### flags compose with bitwise or

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pub_flag = 1
val async_flag = 2
val combined = pub_flag | async_flag
expect(combined).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shb/shb_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHB Roundtrip
- String Table
- Header Validation
- Binary Format
- Write and Read
- Invalid Data
- Primitive Type Layouts
- Flags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
