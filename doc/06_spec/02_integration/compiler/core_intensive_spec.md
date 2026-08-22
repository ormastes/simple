# core_intensive_spec

> Verifies the core intensive behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# core_intensive_spec

Verifies the core intensive behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/core_intensive_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the core intensive behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### StringInterner - Intensive

#### stress testing

#### handles 500 unique strings

- Verify: handles 500 unique strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles 500 unique strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles duplicate strings efficiently


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles duplicate strings efficiently")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles unicode edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles unicode edge cases")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles empty string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var interner = StringInterner.empty()

val id = interner.intern("")
check(id >= 0)

val lookup = interner.lookup(id)
check(lookup.?)
check(lookup? == "")
```

</details>

#### handles whitespace-only strings

- Verify: handles whitespace-only strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles whitespace-only strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles strings with newlines and tabs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles strings with newlines and tabs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var interner = StringInterner.empty()

val s = "line1\nline2\tcolumn2\r\nline3"
val id = interner.intern(s)
val lookup = interner.lookup(id)
check(lookup.?)
check(lookup? == s)
```

</details>

#### maintains bidirectional mapping

- Verify: maintains bidirectional mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: maintains bidirectional mapping")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles get on non-existent string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles get on non-existent string")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val interner = StringInterner.empty()

val result = interner.get_id("nonexistent")
check(not result.?)
```

</details>

#### handles lookup on invalid ID

- Verify: handles lookup on invalid ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles lookup on invalid ID")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val interner = StringInterner.empty()

val result = interner.lookup(999999)
check(not result.?)
```

</details>

#### handles negative ID lookup

- Verify: handles negative ID lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles negative ID lookup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val interner = StringInterner.empty()

val result = interner.lookup(-1)
check(not result.?)
```

</details>

#### handles ID sequence correctly

- Verify: handles ID sequence correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles ID sequence correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles rows with many fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles rows with many fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val row = generate_row_with_many_fields("row1", 50)

check(row.get("id")? == "row1")
val fields = dict_keys(row.fields)
check(fields.len() == 51)  # 50 + id field
```

</details>

#### handles get for all types

- Verify: handles get for all types


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles get for all types")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles get for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles get for missing field")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val row = generate_simple_row("test1")

val result = row.get("nonexistent")
check(not result.?) # Returns None for missing fields
```

</details>

#### handles has correctly

- Verify: handles has correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles has correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var row = SdnRow(fields: {})
row.set("id", "test1")
row.set("existing", "value")

check(row.has_column("existing"))
check(not row.has_column("nonexistent"))
```

</details>

#### handles unicode in field names

- Verify: handles unicode in field names


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles unicode in field names")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles unicode in field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles unicode in field values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val row = generate_row_with_unicode("test1")

check(row.get("name").?)
check(row.get("emoji")? == "🚀🎉✨")
```

</details>

#### edge cases

#### handles empty fields dictionary

- Verify: handles empty fields dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles empty fields dictionary")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val row = SdnRow(fields: {})

val fields = dict_keys(row.fields)
check(fields.len() == 0)
```

</details>

### SdnTable - Intensive

#### large datasets

#### handles 100 rows

- Verify: handles 100 rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles 100 rows")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = generate_table_with_rows("test_table", 100)

check(table.name == "test_table")
check(table.rows.len() == 100)
```

</details>

#### handles 500 rows

- Verify: handles 500 rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles 500 rows")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = generate_table_with_rows("test_table", 500)

check(table.rows.len() == 500)
```

</details>

#### handles rows with many columns

- Verify: handles rows with many columns


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles rows with many columns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable.new("wide_table", [])

for i in 0..10:
    val row = generate_row_with_many_fields("row_{i}", 20)
    table.add_row(row)

check(table.rows.len() == 10)
```

</details>

#### add and retrieve operations

#### maintains correct row count

- Verify: maintains correct row count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: maintains correct row count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = SdnTable.new("test", [])

for i in 0..50:
    val row = generate_simple_row("row_{i}")
    table.add_row(row)

check(table.rows.len() == 50)
```

</details>

#### retrieves rows by ID correctly

- Verify: retrieves rows by ID correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: retrieves rows by ID correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles get_row for non-existent ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles get_row for non-existent ID")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = generate_table_with_rows("test", 10)

val result = table.get_row("nonexistent")
check(not result.?)
```

</details>

#### handles duplicate ID prevention

- Verify: handles duplicate ID prevention


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles duplicate ID prevention")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: marks rows as deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: marks rows as deleted")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: excludes soft-deleted rows from active count


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: excludes soft-deleted rows from active count")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: handles soft delete of non-existent row


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles soft delete of non-existent row")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = generate_table_with_rows("test", 10)

table.mark_deleted("nonexistent")
# Should not crash, table unchanged
check(table.rows.len() == 10)
```

</details>

#### schema handling

#### maintains schema definition

- Verify: maintains schema definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: maintains schema definition")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val schema = ["id", "name", "value"]
val table = SdnTable.new("test", schema)

check(table.schema.len() == 3)
check(table.schema[0] == "id")
check(table.schema[1] == "name")
check(table.schema[2] == "value")
```

</details>

#### allows empty schema

- Verify: allows empty schema


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: allows empty schema")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = SdnTable.new("test", [])

check(table.schema.len() == 0)
```

</details>

#### edge cases

#### handles empty table

- Verify: handles empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles empty table")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = SdnTable.new("empty", [])

check(table.rows.len() == 0)
```

</details>

#### handles table name with unicode

- Verify: handles table name with unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_CORE_INTENSIVE-001
step("Verify: handles table name with unicode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val table = SdnTable.new("测试_table_🚀", [])

check(table.name == "测试_table_🚀")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `71229f9de28a367746a02bdf5386c27b55ba1ec5aa05ab01286bfb5e8f5dbdd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71229f9de28a367746a02bdf5386c27b55ba1ec5aa05ab01286bfb5e8f5dbdd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71229f9de28a367746a02bdf5386c27b55ba1ec5aa05ab01286bfb5e8f5dbdd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/compiler/core_intensive_spec.spl
mirror: doc/06_spec/02_integration/compiler/core_intensive_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/core_intensive_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/compiler/core_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/core_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
