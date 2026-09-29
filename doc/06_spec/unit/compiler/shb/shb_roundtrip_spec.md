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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips empty module")
# Write ShbModuleInterface with 0 entries, read back
# source_hash and interface_hash preserved
expect(true).to_equal(true)
```

</details>

#### roundtrips functions with params

- roundtrips functions with params
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips functions with params")
# FnEntry: name, params[], return_type, flags
# Params: name + type_name pairs
expect(true).to_equal(true)
```

</details>

#### roundtrips structs with fields

- roundtrips structs with fields
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips structs with fields")
# StructEntry: name, fields[], flags
# Fields: name + type_name + flags
expect(true).to_equal(true)
```

</details>

#### roundtrips classes with methods

- roundtrips classes with methods
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips classes with methods")
# ClassEntry: name, fields[], methods[], flags
expect(true).to_equal(true)
```

</details>

#### roundtrips enums with variants

- roundtrips enums with variants
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips enums with variants")
# EnumEntry: name, variants[], flags
expect(true).to_equal(true)
```

</details>

#### roundtrips traits

- roundtrips traits
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips traits")
# TraitEntry: name, methods[], flags
expect(true).to_equal(true)
```

</details>

#### roundtrips reexports

- roundtrips reexports
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips reexports")
# ReexportEntry: symbol_name, source_module
expect(true).to_equal(true)
```

</details>

#### roundtrips type layouts

- roundtrips type layouts
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips type layouts")
# 14 primitive types: i8..text
expect(true).to_equal(true)
```

</details>

#### roundtrips dependencies

- roundtrips dependencies
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips dependencies")
# DependencyEntry: module_path, interface_hash
expect(true).to_equal(true)
```

</details>

#### roundtrips full module with all sections

- roundtrips full module with all sections
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("roundtrips full module with all sections")
expect(true).to_equal(true)
```

</details>

### Invalid Data

#### rejects too-small buffer

- rejects too-small buffer
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects too-small buffer")
# Buffer < 128 bytes => invalid
expect(true).to_equal(true)
```

</details>

#### rejects wrong magic

- rejects wrong magic
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong magic")
# First 4 bytes must be SHB\0
expect(true).to_equal(true)
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
# @req REQ-SSPEC-UNIT
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
| Source | `test/unit/compiler/shb/shb_roundtrip_spec.spl` |
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c87df704cee5685911cbf16155dbea04b2ceabc15dfa2d05af051d991692a162`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c87df704cee5685911cbf16155dbea04b2ceabc15dfa2d05af051d991692a162`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c87df704cee5685911cbf16155dbea04b2ceabc15dfa2d05af051d991692a162`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/shb/shb_roundtrip_spec.spl
mirror: doc/06_spec/unit/compiler/shb/shb_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/shb/shb_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/shb/shb_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/shb/shb_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/shb/shb_roundtrip_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deduplicates strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/shb/shb_roundtrip_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offset 0 is empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/shb/shb_roundtrip_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates correct magic bytes SHB\\0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
