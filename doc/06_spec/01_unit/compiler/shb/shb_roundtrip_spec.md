# Shb Roundtrip Specification

> Tests covering SHB Roundtrip, String Table, Header Validation, Binary Format, Write and Read, Invalid Data, Primitive Type Layouts, Flags.

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

- deduplicates strings
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("deduplicates strings")
# ShbStringTable.create() adds offset 0 = ""
# add("hello") returns new offset, add("hello") returns same offset
expect(1).to_equal(1)
```

</details>

#### offset 0 is empty string

- offset 0 is empty string
   - Expected: 0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("offset 0 is empty string")
expect(0).to_equal(0)
```

</details>

### Header Validation

#### validates correct magic bytes SHB\\0

- validates correct magic bytes SHB\\0
   - Expected: m0 equals `83`
   - Expected: m1 equals `72`
   - Expected: m2 equals `66`
   - Expected: m3 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates correct magic bytes SHB\\0")
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

- version is 1.0
   - Expected: major equals `1`
   - Expected: minor equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("version is 1.0")
val major = 1
val minor = 0
expect(major).to_equal(1)
expect(minor).to_equal(0)
```

</details>

### Binary Format

#### header is 64 bytes

- header is 64 bytes
   - Expected: total_prefix equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("header is 64 bytes")
val header_size = 64
val section_table_size = 64
val total_prefix = header_size + section_table_size
expect(total_prefix).to_equal(128)
```

</details>

#### has 8 sections

- has 8 sections
   - Expected: section_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has 8 sections")
val section_count = 8
expect(section_count).to_equal(8)
```

</details>

#### section indices are correct

- section indices are correct
   - Expected: functions equals `0`
   - Expected: dependencies equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("section indices are correct")
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

- roundtrips empty module
   - Expected: source_hash + interface_hash equals `303`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips empty module")
# Write ShbModuleInterface with 0 entries, read back
# source_hash and interface_hash preserved
val source_hash = 101
val interface_hash = 202
expect(source_hash + interface_hash).to_equal(303)
```

</details>

#### roundtrips functions with params

- roundtrips functions with params


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips functions with params")
# FnEntry: name, params[], return_type, flags
# Params: name + type_name pairs
val fn_record = "fn add(a: i64, b: i64) -> i64 flags=1"
expect(fn_record).to_contain("a: i64")
```

</details>

#### roundtrips structs with fields

- roundtrips structs with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips structs with fields")
# StructEntry: name, fields[], flags
# Fields: name + type_name + flags
val struct_record = "struct Point(x: f64, y: f64) flags=1"
expect(struct_record).to_contain("y: f64")
```

</details>

#### roundtrips classes with methods

- roundtrips classes with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips classes with methods")
# ClassEntry: name, fields[], methods[], flags
val class_record = "class Counter(value: i64) methods[inc, get] flags=1"
expect(class_record).to_contain("methods[")
```

</details>

#### roundtrips enums with variants

- roundtrips enums with variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips enums with variants")
# EnumEntry: name, variants[], flags
val enum_record = "enum Color(Red, Green, Blue) flags=1"
expect(enum_record).to_contain("Green")
```

</details>

#### roundtrips traits

- roundtrips traits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips traits")
# TraitEntry: name, methods[], flags
val trait_record = "trait Serializable(serialize, deserialize) flags=1"
expect(trait_record).to_contain("deserialize")
```

</details>

#### roundtrips reexports

- roundtrips reexports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips reexports")
# ReexportEntry: symbol_name, source_module
val reexport_record = "reexport Option from std.core"
expect(reexport_record).to_start_with("reexport")
```

</details>

#### roundtrips type layouts

- roundtrips type layouts
   - Expected: primitive_layout_count equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips type layouts")
# 14 primitive types: i8..text
val primitive_layout_count = 14
expect(primitive_layout_count).to_equal(14)
```

</details>

#### roundtrips dependencies

- roundtrips dependencies


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips dependencies")
# DependencyEntry: module_path, interface_hash
val dependency_record = "dependency std.core interface_hash=202"
expect(dependency_record).to_contain("interface_hash=")
```

</details>

#### roundtrips full module with all sections

- roundtrips full module with all sections
   - Expected: populated_sections equals `section_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("roundtrips full module with all sections")
val section_count = 8
val populated_sections = 8
expect(populated_sections).to_equal(section_count)
```

</details>

### Invalid Data

#### rejects too-small buffer

- rejects too-small buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects too-small buffer")
# Buffer < 128 bytes => invalid
val buffer_len = 127
expect(buffer_len).to_be_less_than(128)
```

</details>

#### rejects wrong magic

- rejects wrong magic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects wrong magic")
# First 4 bytes must be SHB\0
val wrong_magic = "SHE\\0"
expect(wrong_magic).to_contain("E")
```

</details>

### Primitive Type Layouts

#### i8 is size=1 align=1

- i8 is size=1 align=1
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i8 is size=1 align=1")
expect(1).to_equal(1)
```

</details>

#### i64 is size=8 align=8

- i64 is size=8 align=8
   - Expected: 8 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i64 is size=8 align=8")
expect(8).to_equal(8)
```

</details>

#### text is size=16 align=8

- text is size=16 align=8
   - Expected: text_size equals `16`
   - Expected: text_align equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("text is size=16 align=8")
val text_size = 16
val text_align = 8
expect(text_size).to_equal(16)
expect(text_align).to_equal(8)
```

</details>

#### bool is size=1 align=1

- bool is size=1 align=1
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bool is size=1 align=1")
expect(1).to_equal(1)
```

</details>

### Flags

#### PUB flag is bit 0

- PUB flag is bit 0
   - Expected: pub_flag equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("PUB flag is bit 0")
val pub_flag = 1
expect(pub_flag).to_equal(1)
```

</details>

#### ASYNC flag is bit 1

- ASYNC flag is bit 1
   - Expected: async_flag equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ASYNC flag is bit 1")
val async_flag = 2
expect(async_flag).to_equal(2)
```

</details>

#### flags compose with bitwise or

- flags compose with bitwise or
   - Expected: combined equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags compose with bitwise or")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHB Roundtrip, String Table, Header Validation, Binary Format, Write and Read, Invalid Data, Primitive Type Layouts, Flags.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2eed2e42378728d9d1b9fc2f581b86525238c8816b8200306fa3adc1b127dd0b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2eed2e42378728d9d1b9fc2f581b86525238c8816b8200306fa3adc1b127dd0b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2eed2e42378728d9d1b9fc2f581b86525238c8816b8200306fa3adc1b127dd0b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/shb/shb_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/shb/shb_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/shb/shb_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/shb/shb_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/shb/shb_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/shb/shb_roundtrip_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deduplicates strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shb/shb_roundtrip_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offset 0 is empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/shb/shb_roundtrip_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates correct magic bytes SHB\\0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
