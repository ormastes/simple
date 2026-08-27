# Semihosting System API Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semihosting System API Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/features/baremetal/semihosting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Semihosting Operations

#### standard operations

#### exposes SYS_OPEN and SYS_CLOSE

- exposes SYS_OPEN and SYS_CLOSE


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes SYS_OPEN and SYS_CLOSE")
check(SemihostOp.SYS_OPEN() == 0x01)
check(SemihostOp.SYS_CLOSE() == 0x02)
```

</details>

#### exposes SYS_WRITE and SYS_READ

- exposes SYS_WRITE and SYS_READ


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes SYS_WRITE and SYS_READ")
check(SemihostOp.SYS_WRITE() == 0x05)
check(SemihostOp.SYS_READ() == 0x06)
```

</details>

#### exposes SYS_CLOCK, SYS_TIME, and SYS_EXIT

- exposes SYS_CLOCK, SYS_TIME, and SYS_EXIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes SYS_CLOCK, SYS_TIME, and SYS_EXIT")
check(SemihostOp.SYS_CLOCK() == 0x10)
check(SemihostOp.SYS_TIME() == 0x11)
check(SemihostOp.SYS_EXIT() == 0x18)
```

</details>

#### extended operations

#### exposes extended write handles

- exposes extended write handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes extended write handles")
check(SemihostOp.SYS_WRITE_HANDLE() == 0x100)
check(SemihostOp.SYS_WRITE_HANDLE_P1() == 0x101)
check(SemihostOp.SYS_WRITE_HANDLE_P2() == 0x102)
check(SemihostOp.SYS_WRITE_HANDLE_P3() == 0x103)
check(SemihostOp.SYS_WRITE_HANDLE_PN() == 0x104)
```

</details>

### Format Types

#### integer and float codes

#### exposes integer format codes

- exposes integer format codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes integer format codes")
check(FormatType.Int8() == 1)
check(FormatType.Int16() == 2)
check(FormatType.Int32() == 3)
check(FormatType.Int64() == 4)
check(FormatType.UInt8() == 5)
check(FormatType.UInt16() == 6)
check(FormatType.UInt32() == 7)
check(FormatType.UInt64() == 8)
```

</details>

#### exposes float format codes

- exposes float format codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes float format codes")
check(FormatType.Float32() == 9)
check(FormatType.Float64() == 10)
```

</details>

#### special and hex codes

#### exposes special codes

- exposes special codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes special codes")
check(FormatType.Bool() == 11)
check(FormatType.Char() == 12)
check(FormatType.Pointer() == 18)
check(FormatType.Text() == 19)
```

</details>

#### exposes hex codes

- exposes hex codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes hex codes")
check(FormatType.Hex8() == 13)
check(FormatType.Hex16() == 14)
check(FormatType.Hex32() == 15)
check(FormatType.Hex64() == 16)
```

</details>

### String Intern Table

#### creation

#### creates an empty table

- creates an empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates an empty table")
val table = StringInternTable.new()
check(table.count() == 0)
```

</details>

#### creates a table with test handles

- creates a table with test handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a table with test handles")
val table = StringInternTable.with_test_handles()
check(table.count() == 4)
check(table.get(0xFFFF0001) != nil)
check(table.get(0xFFFF0004) != nil)
```

</details>

#### interning

#### deduplicates identical strings

- deduplicates identical strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deduplicates identical strings")
var table = StringInternTable.new()
val h1 = table.intern("Hello", [])
val h2 = table.intern("Hello", [])
check(h1 == h2)
check(table.count() == 1)
```

</details>

#### assigns different handles to different strings

- assigns different handles to different strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assigns different handles to different strings")
var table = StringInternTable.new()
val h1 = table.intern("Hello", [])
val h2 = table.intern("World", [])
check(h1 != h2)
check(table.count() == 2)
```

</details>

#### stores format types

- stores format types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores format types")
var table = StringInternTable.new()
val handle = table.intern("Count: {}", [FormatType.Int64()])
val entry = table.get(handle).unwrap()
check(entry.param_count() == 1)
check(entry.format_types[0] == FormatType.Int64())
```

</details>

#### stores source information

- stores source information


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores source information")
var table = StringInternTable.new()
val handle = table.intern_with_source("Debug: {}", [FormatType.Int32()], "test.spl", 42)
val entry = table.get(handle).unwrap()
check(entry.source_file != nil)
check_text(entry.source_file.unwrap(), "test.spl")
check(entry.source_line == 42)
```

</details>

### String Intern Entry

#### entry helpers

#### creates entry with handle and text

- creates entry with handle and text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates entry with handle and text")
val entry = StringInternEntry.new(42, "Hello {}", [FormatType.Text()])
check(entry.handle == 42)
check_text(entry.text, "Hello {}")
check(entry.param_count() == 1)
```

</details>

#### creates entry with source location

- creates entry with source location


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates entry with source location")
val entry = StringInternEntry.with_source(1, "Test", [], "file.spl", 10)
check(entry.source_file != nil)
check(entry.source_line == 10)
```

</details>

#### reports parameter counts

- reports parameter counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports parameter counts")
val entry = StringInternEntry.new(1, "{} + {} = {}", [FormatType.Int64(), FormatType.Int64(), FormatType.Int64()])
check(entry.param_count() == 3)
check(entry.has_params())
```

</details>

### Binary Serialization

#### write section

#### writes empty table

- writes empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes empty table")
val table = StringInternTable.new()
val bytes = write_string_intern_section(table)
check(bytes.len() >= 6)
```

</details>

#### writes entries into the section

- writes entries into the section


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes entries into the section")
var table = StringInternTable.new()
table.intern("Hello", [])
table.intern("World {}", [FormatType.Int64()])
val bytes = write_string_intern_section(table)
check(bytes.len() > 10)
```

</details>

#### read section

#### reads back a serialized table shape

- reads back a serialized table shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads back a serialized table shape")
var original = StringInternTable.new()
original.intern("Hello", [])
original.intern("World {}", [FormatType.Int64()])
val bytes = write_string_intern_section(original)
val restored = read_string_intern_section(bytes)
check(restored.count() == 2)
check(restored.get(1) != nil)
check(restored.get(2) != nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0facda51f71b16df2468d9fc58b5205a38d90c0e313248643c41bc0edce86b95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0facda51f71b16df2468d9fc58b5205a38d90c0e313248643c41bc0edce86b95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0facda51f71b16df2468d9fc58b5205a38d90c0e313248643c41bc0edce86b95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/baremetal/semihosting_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/semihosting_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/semihosting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/semihosting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/semihosting_spec.spl:200:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes SYS_OPEN and SYS_CLOSE' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/semihosting_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes SYS_WRITE and SYS_READ' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/semihosting_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes SYS_CLOCK, SYS_TIME, and SYS_EXIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
