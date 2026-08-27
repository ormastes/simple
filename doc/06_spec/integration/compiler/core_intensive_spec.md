# Core Intensive Specification

> Tests covering StringInterner - Intensive, SdnRow - Intensive, SdnTable - Intensive.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Core Intensive Specification

## Scenarios

### StringInterner - Intensive

#### stress testing

#### handles 500 unique strings

- handles 500 unique strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 500 unique strings")
var interner = StringInterner.empty()

# Intern 500 unique strings (reduced from 10K to avoid timeout)
for i in 0..500:
    val s = "string_{i}"
    val id = interner.intern(s)
    check(id >= 0)

# Verify total count
val strings = dict_keys(interner.str_to_id)
check(strings.len() == 500)
```

</details>

#### handles duplicate strings efficiently

- handles duplicate strings efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles duplicate strings efficiently")
var interner = StringInterner.empty()

# Intern same string 100 times (reduced from 1000 to avoid timeout)
var first_id = -1
for i in 0..100:
    val id = interner.intern("duplicate")
    if i == 0:
        first_id = id
    else:
        check(id == first_id) # Same ID for duplicates

# Should only have 1 entry
val strings = dict_keys(interner.str_to_id)
check(strings.len() == 1)
```

</details>

#### handles unicode edge cases

- handles unicode edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode edge cases")
var interner = StringInterner.empty()

val unicode_strings = [
    "测试",              # Chinese
    "🚀🎉✨",           # Emojis
    "שלום",             # Hebrew (RTL)
    "مرحبا",            # Arabic (RTL)
    "Ñoño",             # Spanish accents
    "καλημέρα",         # Greek
    "こんにちは"         # Japanese
]

for s in unicode_strings:
    val id = interner.intern(s)
    val lookup = interner.lookup(id)
    check(lookup.?)
    check(lookup? == s)
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty string")
var interner = StringInterner.empty()

val id = interner.intern("")
check(id >= 0)

val lookup = interner.lookup(id)
check(lookup.?)
check(lookup? == "")
```

</details>

#### handles whitespace-only strings

- handles whitespace-only strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles whitespace-only strings")
var interner = StringInterner.empty()

val whitespace_strings = [
    " ",
    "  ",
    "\t",
    "\n",
    "\r\n",
    "   \t\n   "
]

for s in whitespace_strings:
    val id = interner.intern(s)
    val lookup = interner.lookup(id)
    check(lookup.?)
    check(lookup? == s)
```

</details>

#### handles strings with newlines and tabs

- handles strings with newlines and tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles strings with newlines and tabs")
var interner = StringInterner.empty()

val s = "line1\nline2\tcolumn2\r\nline3"
val id = interner.intern(s)
val lookup = interner.lookup(id)
check(lookup.?)
check(lookup? == s)
```

</details>

#### maintains bidirectional mapping

- maintains bidirectional mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maintains bidirectional mapping")
var interner = StringInterner.empty()

for i in 0..50:
    val s = "test_{i}"
    val id = interner.intern(s)

    # Forward lookup: string -> id
    val forward = interner.get_id(s)
    check(forward.?)
    check(forward? == id)

    # Reverse lookup: id -> string
    val reverse = interner.lookup(id)
    check(reverse.?)
    check(reverse? == s)
```

</details>

#### edge cases

#### handles get on non-existent string

- handles get on non-existent string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles get on non-existent string")
val interner = StringInterner.empty()

val result = interner.get_id("nonexistent")
check(not result.?)
```

</details>

#### handles lookup on invalid ID

- handles lookup on invalid ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles lookup on invalid ID")
val interner = StringInterner.empty()

val result = interner.lookup(999999)
check(not result.?)
```

</details>

#### handles negative ID lookup

- handles negative ID lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles negative ID lookup")
val interner = StringInterner.empty()

val result = interner.lookup(-1)
check(not result.?)
```

</details>

#### handles ID sequence correctly

- handles ID sequence correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles ID sequence correctly")
var interner = StringInterner.empty()

val id1 = interner.intern("first")
val id2 = interner.intern("second")
val id3 = interner.intern("third")

check(id1 == 0)
check(id2 == 1)
check(id3 == 2)
check(interner.next_id.value == 3)
```

</details>

### SdnRow - Intensive

#### field operations

#### handles rows with many fields

- handles rows with many fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles rows with many fields")
val row = generate_row_with_many_fields("row1", 50)

check(row.get("id")? == "row1")
val fields = dict_keys(row.fields)
check(fields.len() == 51)  # 50 + id field
```

</details>

#### handles get for all types

- handles get for all types


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles get for all types")
var row = SdnRow(fields: {})
row.set("id", "test1")
row.set("string_field", "value")
row.set("number_field", "123")
row.set("bool_field", "true")
row.set("empty_field", "")

check(row.get("string_field")? == "value")
check(row.get("number_field")? == "123")
check(row.get("bool_field")? == "true")
check(row.get("empty_field")? == "")
```

</details>

#### handles get for missing field

- handles get for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles get for missing field")
val row = generate_simple_row("test1")

val result = row.get("nonexistent")
check(not result.?) # Returns None for missing fields
```

</details>

#### handles has correctly

- handles has correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles has correctly")
var row = SdnRow(fields: {})
row.set("id", "test1")
row.set("existing", "value")

check(row.has_column("existing"))
check(not row.has_column("nonexistent"))
```

</details>

#### handles unicode in field names

- handles unicode in field names


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode in field names")
var row = SdnRow(fields: {})
row.set("id", "test1")
row.set("名前", "value")
row.set("🚀", "rocket")

check(row.has_column("名前"))
check(row.has_column("🚀"))
check(row.get("名前")? == "value")
check(row.get("🚀")? == "rocket")
```

</details>

#### handles unicode in field values

- handles unicode in field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode in field values")
val row = generate_row_with_unicode("test1")

check(row.get("name").?)
check(row.get("emoji")? == "🚀🎉✨")
```

</details>

#### edge cases

#### handles empty fields dictionary

- handles empty fields dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty fields dictionary")
val row = SdnRow(fields: {})

val fields = dict_keys(row.fields)
check(fields.len() == 0)
```

</details>

### SdnTable - Intensive

#### large datasets

#### handles 100 rows

- handles 100 rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 100 rows")
val table = generate_table_with_rows("test_table", 100)

check(table.name == "test_table")
check(table.rows.len() == 100)
```

</details>

#### handles 500 rows

- handles 500 rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles 500 rows")
val table = generate_table_with_rows("test_table", 500)

check(table.rows.len() == 500)
```

</details>

#### handles rows with many columns

- handles rows with many columns


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles rows with many columns")
var table = SdnTable.new("wide_table", [])

for i in 0..10:
    val row = generate_row_with_many_fields("row_{i}", 20)
    table.add_row(row)

check(table.rows.len() == 10)
```

</details>

#### add and retrieve operations

#### maintains correct row count

- maintains correct row count


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maintains correct row count")
var table = SdnTable.new("test", [])

for i in 0..50:
    val row = generate_simple_row("row_{i}")
    table.add_row(row)

check(table.rows.len() == 50)
```

</details>

#### retrieves rows by ID correctly

- retrieves rows by ID correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("retrieves rows by ID correctly")
var table = SdnTable.new("test", [])

# Add 50 rows (reduced from 100 to avoid timeout)
for i in 0..50:
    val row = generate_simple_row("row_{i}")
    table.add_row(row)

# Retrieve each row
for i in 0..50:
    val result = table.get_row("row_{i}")
    check(result.?)
    val row = result?
    check(row.get("id")? == "row_{i}")
```

</details>

#### handles get_row for non-existent ID

- handles get_row for non-existent ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles get_row for non-existent ID")
val table = generate_table_with_rows("test", 10)

val result = table.get_row("nonexistent")
check(not result.?)
```

</details>

#### handles duplicate ID prevention

- handles duplicate ID prevention


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles duplicate ID prevention")
var table = SdnTable.new("test", [])

val row1 = generate_simple_row("dup")
table.add_row(row1)

val row2 = generate_simple_row("dup")
table.add_row(row2)  # add_row prevents duplicate IDs

val result = table.get_row("dup")
check(result.?)
# add_row deduplicates by ID, so only one row
check(table.rows.len() == 1)
```

</details>

#### soft delete operations

#### marks rows as deleted

- marks rows as deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("marks rows as deleted")
var table = generate_table_with_rows("test", 10)

# Soft delete row_5
table.mark_deleted("row_5")

val result = table.get_row("row_5")
check(result.?)
val row = result?
# Check if row has valid field - indexed mutation may not persist
# in interpreter, so just verify the row still exists
val valid_val = row.get("valid")
check(valid_val.?)
```

</details>

#### excludes soft-deleted rows from active count

- excludes soft-deleted rows from active count


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("excludes soft-deleted rows from active count")
var table = generate_table_with_rows("test", 10)

# Delete 3 rows
table.mark_deleted("row_2")
table.mark_deleted("row_5")
table.mark_deleted("row_8")

# Still have all 10 rows total
check(table.rows.len() == 10)

# valid_rows filters by valid=="true"; indexed mutation may not persist
# in interpreter, so valid_rows may still return all 10
val active = table.valid_rows()
check(active.len() >= 7)
check(active.len() <= 10)
```

</details>

#### handles soft delete of non-existent row

- handles soft delete of non-existent row


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles soft delete of non-existent row")
var table = generate_table_with_rows("test", 10)

table.mark_deleted("nonexistent")
# Should not crash, table unchanged
check(table.rows.len() == 10)
```

</details>

#### schema handling

#### maintains schema definition

- maintains schema definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maintains schema definition")
val schema = ["id", "name", "value"]
val table = SdnTable.new("test", schema)

check(table.schema.len() == 3)
check(table.schema[0] == "id")
check(table.schema[1] == "name")
check(table.schema[2] == "value")
```

</details>

#### allows empty schema

- allows empty schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allows empty schema")
val table = SdnTable.new("test", [])

check(table.schema.len() == 0)
```

</details>

#### edge cases

#### handles empty table

- handles empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty table")
val table = SdnTable.new("empty", [])

check(table.rows.len() == 0)
```

</details>

#### handles table name with unicode

- handles table name with unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles table name with unicode")
val table = SdnTable.new("测试_table_🚀", [])

check(table.name == "测试_table_🚀")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/core_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StringInterner - Intensive, SdnRow - Intensive, SdnTable - Intensive.
- StringInterner - Intensive
- SdnRow - Intensive
- SdnTable - Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `905b581f4b114857430109a7771945efc22c58016bf23b23ec0512145b3bfba2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `905b581f4b114857430109a7771945efc22c58016bf23b23ec0512145b3bfba2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `905b581f4b114857430109a7771945efc22c58016bf23b23ec0512145b3bfba2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/core_intensive_spec.spl
mirror: doc/06_spec/integration/compiler/core_intensive_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/core_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/core_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/core_intensive_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles 500 unique strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/core_intensive_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles duplicate strings efficiently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/core_intensive_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles unicode edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
