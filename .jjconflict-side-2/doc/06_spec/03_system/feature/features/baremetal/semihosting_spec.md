# Semihosting System API Specification

> 1. check

<!-- sdn-diagram:id=semihosting_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semihosting_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semihosting_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semihosting_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Semihosting Operations

#### standard operations

#### exposes SYS_OPEN and SYS_CLOSE

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(SemihostOp.SYS_OPEN() == 0x01)
check(SemihostOp.SYS_CLOSE() == 0x02)
```

</details>

#### exposes SYS_WRITE and SYS_READ

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(SemihostOp.SYS_WRITE() == 0x05)
check(SemihostOp.SYS_READ() == 0x06)
```

</details>

#### exposes SYS_CLOCK, SYS_TIME, and SYS_EXIT

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(SemihostOp.SYS_CLOCK() == 0x10)
check(SemihostOp.SYS_TIME() == 0x11)
check(SemihostOp.SYS_EXIT() == 0x18)
```

</details>

#### extended operations

#### exposes extended write handles

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check
4. check
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(FormatType.Float32() == 9)
check(FormatType.Float64() == 10)
```

</details>

#### special and hex codes

#### exposes special codes

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(FormatType.Bool() == 11)
check(FormatType.Char() == 12)
check(FormatType.Pointer() == 18)
check(FormatType.Text() == 19)
```

</details>

#### exposes hex codes

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(FormatType.Hex8() == 13)
check(FormatType.Hex16() == 14)
check(FormatType.Hex32() == 15)
check(FormatType.Hex64() == 16)
```

</details>

### String Intern Table

#### creation

#### creates an empty table

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = StringInternTable.new()
check(table.count() == 0)
```

</details>

#### creates a table with test handles

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = StringInternTable.with_test_handles()
check(table.count() == 4)
check(table.get(0xFFFF0001).? == true)
check(table.get(0xFFFF0004).? == true)
```

</details>

#### interning

#### deduplicates identical strings

1. var table = StringInternTable new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = StringInternTable.new()
val h1 = table.intern("Hello", [])
val h2 = table.intern("Hello", [])
check(h1 == h2)
check(table.count() == 1)
```

</details>

#### assigns different handles to different strings

1. var table = StringInternTable new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = StringInternTable.new()
val h1 = table.intern("Hello", [])
val h2 = table.intern("World", [])
check(h1 != h2)
check(table.count() == 2)
```

</details>

#### stores format types

1. var table = StringInternTable new
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = StringInternTable.new()
val handle = table.intern("Count: {}", [FormatType.Int64()])
val entry = table.get(handle).unwrap()
check(entry.param_count() == 1)
check(entry.format_types[0] == FormatType.Int64())
```

</details>

#### stores source information

1. var table = StringInternTable new
2. check
3. check text
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = StringInternTable.new()
val handle = table.intern_with_source("Debug: {}", [FormatType.Int32()], "test.spl", 42)
val entry = table.get(handle).unwrap()
check(entry.source_file.? == true)
check_text(entry.source_file.unwrap(), "test.spl")
check(entry.source_line == 42)
```

</details>

### String Intern Entry

#### entry helpers

#### creates entry with handle and text

1. check
2. check text
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = StringInternEntry.new(42, "Hello {}", [FormatType.Text()])
check(entry.handle == 42)
check_text(entry.text, "Hello {}")
check(entry.param_count() == 1)
```

</details>

#### creates entry with source location

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = StringInternEntry.with_source(1, "Test", [], "file.spl", 10)
check(entry.source_file.? == true)
check(entry.source_line == 10)
```

</details>

#### reports parameter counts

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = StringInternEntry.new(1, "{} + {} = {}", [FormatType.Int64(), FormatType.Int64(), FormatType.Int64()])
check(entry.param_count() == 3)
check(entry.has_params())
```

</details>

### Binary Serialization

#### write section

#### writes empty table

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = StringInternTable.new()
val bytes = write_string_intern_section(table)
check(bytes.len() >= 6)
```

</details>

#### writes entries into the section

1. var table = StringInternTable new
2. table intern
3. table intern
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = StringInternTable.new()
table.intern("Hello", [])
table.intern("World {}", [FormatType.Int64()])
val bytes = write_string_intern_section(table)
check(bytes.len() > 10)
```

</details>

#### read section

#### reads back a serialized table shape

1. var original = StringInternTable new
2. original intern
3. original intern
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var original = StringInternTable.new()
original.intern("Hello", [])
original.intern("World {}", [FormatType.Int64()])
val bytes = write_string_intern_section(original)
val restored = read_string_intern_section(bytes)
check(restored.count() == 2)
check(restored.get(1).? == true)
check(restored.get(2).? == true)
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
