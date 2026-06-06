# Database Core Specification

> 1. var interner = StringInterner

<!-- sdn-diagram:id=database_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_core_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Core Specification

## Scenarios

### StringInterner

#### interns same string to same ID

1. var interner = StringInterner
   - Expected: id1 equals `id2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id1 = interner.intern("test")
val id2 = interner.intern("test")

expect(id1).to_equal(id2)
```

</details>

#### interns different strings to different IDs

1. var interner = StringInterner


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id1 = interner.intern("first")
val id2 = interner.intern("second")

expect(id1).to_not_equal(id2)
```

</details>

#### lookups strings by ID

1. var interner = StringInterner
   - Expected: result.? is true
   - Expected: result? equals `lookup_test`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id = interner.intern("lookup_test")
val result = interner.lookup(id)

expect(result.?).to_equal(true)
expect(result?).to_equal("lookup_test")
```

</details>

#### lookups IDs by string

1. var interner = StringInterner
   - Expected: result.? is true
   - Expected: result? equals `id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id = interner.intern("reverse_lookup")
val result = interner.get_id("reverse_lookup")

expect(result.?).to_equal(true)
expect(result?).to_equal(id)
```

</details>

#### returns None for unknown ID

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val result = interner.lookup(999)
expect(result.?).to_equal(false)
```

</details>

#### returns None for unknown string

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val result = interner.get_id("nonexistent")
expect(result.?).to_equal(false)
```

</details>

#### handles empty strings

1. var interner = StringInterner
   - Expected: result.? is true
   - Expected: result? equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id = interner.intern("")
val result = interner.lookup(id)

expect(result.?).to_equal(true)
expect(result?).to_equal("")
```

</details>

#### handles unicode strings

1. var interner = StringInterner
   - Expected: result.? is true
   - Expected: value contains `世界"`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

val id = interner.intern("Hello 世界 🌍")
val result = interner.lookup(id)

expect(result.?).to_equal(true)
val value = result ?? ""
expect(value.contains("世界")).to_equal(true)
```

</details>

#### increments ID counter

1. var interner = StringInterner
   - Expected: interner.next_id equals `0`

2. interner intern
   - Expected: interner.next_id equals `1`

3. interner intern
   - Expected: interner.next_id equals `2`

4. interner intern
   - Expected: interner.next_id equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

expect(interner.next_id).to_equal(0)

interner.intern("first")
expect(interner.next_id).to_equal(1)

interner.intern("second")
expect(interner.next_id).to_equal(2)

# Interning same string doesn't increment
interner.intern("first")
expect(interner.next_id).to_equal(2)
```

</details>

### SdnRow

#### creates empty row

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = SdnRow(fields: {})
expect(row.fields.len()).to_equal(0)
```

</details>

#### sets and gets field values

1. var row = SdnRow

2. row set

3. row set
   - Expected: row.get("name")? equals `Alice`
   - Expected: row.get("age")? equals `30`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})

row.set("name", "Alice")
row.set("age", "30")

expect(row.get("name")?).to_equal("Alice")
expect(row.get("age")?).to_equal("30")
```

</details>

#### returns None for missing field

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = SdnRow(fields: {})
val result = row.get("nonexistent")

expect(result.?).to_equal(false)
```

</details>

#### gets field as i64

1. var row = SdnRow

2. row set
   - Expected: result.? is true
   - Expected: result? equals `42`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("count", "42")

val result = row.get_i64("count")
expect(result.?).to_equal(true)
expect(result?).to_equal(42)
```

</details>

#### gets field as bool

1. var row = SdnRow

2. row set

3. row set
   - Expected: row.get_bool("flag")? is true
   - Expected: row.get_bool("other")? is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("flag", "true")
row.set("other", "false")

expect(row.get_bool("flag")?).to_equal(true)
expect(row.get_bool("other")?).to_equal(false)
```

</details>

#### handles large field values

1. var row = SdnRow

2. row set
   - Expected: result.len() equals `10000`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})

val large_text = "x".repeat(10000)
row.set("large", large_text)

val result = row.get("large")?
expect(result.len()).to_equal(10000)
```

</details>

#### overwrites existing field

1. var row = SdnRow

2. row set

3. row set
   - Expected: row.get("key")? equals `new_value`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})

row.set("key", "old_value")
row.set("key", "new_value")

expect(row.get("key")?).to_equal("new_value")
```

</details>

### SdnTable

#### creates table with schema

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable(name: "users", columns: ["id", "name", "email"], rows: [], index: {})

expect(table.name).to_equal("users")
expect(table.columns.len()).to_equal(3)
expect(table.rows.len()).to_equal(0)
```

</details>

#### adds row to table

1. var table = SdnTable

2. var row = SdnRow

3. row set

4. row set

5. table add row
   - Expected: table.rows.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "items", columns: ["id", "value"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "1")
row.set("value", "test")

table.add_row(row)
expect(table.rows.len()).to_equal(1)
```

</details>

#### adds multiple rows

1. var table = SdnTable

2. var row = SdnRow

3. row set

4. row set

5. table add row
   - Expected: table.rows.len() equals `5`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "data", columns: ["key", "value"], rows: [], index: {})

for i in 0..5:
    var row = SdnRow(fields: {})
    row.set("key", "key_{i}")
    row.set("value", "value_{i}")
    table.add_row(row)

expect(table.rows.len()).to_equal(5)
```

</details>

#### gets row by ID

1. var table = SdnTable

2. var row = SdnRow

3. row set

4. row set

5. table add row
   - Expected: result.? is true
   - Expected: data equals `test_data`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "records", columns: ["id", "data"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "record_123")
row.set("data", "test_data")
table.add_row(row)

val result = table.get_row("record_123")
expect(result.?).to_equal(true)
val r1 = result ?? SdnRow(fields: {})
val data = r1.get("data") ?? ""
expect(data).to_equal("test_data")
```

</details>

#### returns None for missing row ID

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable(name: "empty", columns: ["id"], rows: [], index: {})
val result = table.get_row("nonexistent")

expect(result.?).to_equal(false)
```

</details>

#### marks row as deleted

1. var table = SdnTable

2. var row = SdnRow

3. row set

4. row set

5. row set

6. table add row

7. table mark deleted
   - Expected: result.? is true
   - Expected: valid equals `false`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "soft_delete", columns: ["id", "value", "valid"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "delete_me")
row.set("value", "data")
row.set("valid", "true")
table.add_row(row)

# Mark as deleted
table.mark_deleted("delete_me")

# Row still exists but marked invalid
val result = table.get_row("delete_me")
expect(result.?).to_equal(true)
val r2 = result ?? SdnRow(fields: {})
val valid = r2.get("valid") ?? ""
expect(valid).to_equal("false")
```

</details>

#### filters valid rows only

1. var table = SdnTable

2. var row = SdnRow

3. row set

4. row set

5. table add row
   - Expected: valid_rows.len() equals `3)  # Rows 0, 2, 4`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "mixed", columns: ["id", "valid"], rows: [], index: {})

# Add some valid and invalid rows
for i in 0..5:
    var row = SdnRow(fields: {})
    row.set("id", "row_{i}")
    val valid_str = if i % 2 == 0: "true" else: "false"
    row.set("valid", valid_str)
    table.add_row(row)

val valid_rows = table.valid_rows()
expect(valid_rows.len()).to_equal(3)  # Rows 0, 2, 4
```

</details>

#### handles empty table

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable(name: "empty", columns: ["id"], rows: [], index: {})

expect(table.rows.len()).to_equal(0)
expect(table.valid_rows().len()).to_equal(0)

val result = table.get_row("any_id")
expect(result.?).to_equal(false)
```

</details>

### SdnDatabase

#### creates new database

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = SdnDatabase(path: "/tmp/test_new_db.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

expect(db.tables.len()).to_equal(0)
```

</details>

#### adds table to database

1. var db = SdnDatabase

2. db set table
   - Expected: db.tables.len() equals `1`
   - Expected: db.tables.has("test_table") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_add_table.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

val table = SdnTable(name: "test_table", columns: ["id", "value"], rows: [], index: {})
db.set_table("test_table", table)

expect(db.tables.len()).to_equal(1)
expect(db.tables.has("test_table")).to_equal(true)
```

</details>

#### gets table from database

1. var db = SdnDatabase

2. db set table
   - Expected: result.? is true
   - Expected: tbl.name equals `my_table`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_get_table.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

val table = SdnTable(name: "my_table", columns: ["col1", "col2"], rows: [], index: {})
db.set_table("my_table", table)

val result = db.get_table("my_table")
expect(result.?).to_equal(true)
val tbl = result ?? SdnTable(name: "", columns: [], rows: [], index: {})
expect(tbl.name).to_equal("my_table")
```

</details>

#### gets mutable table

1. var db = SdnDatabase

2. db set table

3. var table opt = db get table mut
   - Expected: table_opt.? is true

4. var row = SdnRow

5. row set

6. mut table add row

7. db set table
   - Expected: final_table.rows.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_mut_table.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

val table = SdnTable(name: "mut_table", columns: ["id"], rows: [], index: {})
db.set_table("mut_table", table)

var table_opt = db.get_table_mut("mut_table")
expect(table_opt.?).to_equal(true)

var mut_table = table_opt?
var row = SdnRow(fields: {})
row.set("id", "test")
mut_table.add_row(row)

# Must put back for changes to persist
db.set_table("mut_table", mut_table)

# Verify change persisted
val final_table = db.get_table("mut_table")?
expect(final_table.rows.len()).to_equal(1)
```

</details>

#### returns None for missing table

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = SdnDatabase(path: "/tmp/test_missing.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

val result = db.get_table("nonexistent")
expect(result.?).to_equal(false)
```

</details>

#### replaces existing table

1. var db = SdnDatabase

2. db set table

3. db set table
   - Expected: result.columns.len() equals `1`
   - Expected: result.columns[0] equals `new_col`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_replace.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

# Add initial table
val table1 = SdnTable(name: "replaceable", columns: ["old_col"], rows: [], index: {})
db.set_table("replaceable", table1)

# Replace with new table
val table2 = SdnTable(name: "replaceable", columns: ["new_col"], rows: [], index: {})
db.set_table("replaceable", table2)

# Verify replacement
val result = db.get_table("replaceable")?
expect(result.columns.len()).to_equal(1)
expect(result.columns[0]).to_equal("new_col")
```

</details>

#### saves and loads database

1. file delete

2. var db1 = SdnDatabase

3. var table = SdnTable

4. var row = SdnRow

5. row set

6. row set

7. table add row

8. db1 set table

9. db1 save
   - Expected: db2_opt.? is true
   - Expected: loaded_table.rows.len() equals `1`
   - Expected: loaded_row.get("value")? equals `test_value`

10. file delete


<details>
<summary>Executable SPipe</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/test_save_load.sdn"

# Clean up if exists
if file_exists(db_path):
    file_delete(db_path)

# Create and populate database
var db1 = SdnDatabase(path: db_path, tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)
var table = SdnTable(name: "test", columns: ["id", "value"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "save_001")
row.set("value", "test_value")
table.add_row(row)

db1.set_table("test", table)
db1.save()

# Load database
val db2_opt = SdnDatabase.load(db_path)
expect(db2_opt.?).to_equal(true)

val db2 = db2_opt?
val loaded_table = db2.get_table("test")?
expect(loaded_table.rows.len()).to_equal(1)

val loaded_row = loaded_table.get_row("save_001")?
expect(loaded_row.get("value")?).to_equal("test_value")

# Cleanup
file_delete(db_path)
```

</details>

#### handles multiple tables

1. var db = SdnDatabase

2. db set table
   - Expected: db.tables.len() equals `5`
   - Expected: table_opt.? is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_multi_tables.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

# Add multiple tables
for i in 0..5:
    val table = SdnTable(name: "table_{i}", columns: ["col_{i}"], rows: [], index: {})
    db.set_table("table_{i}", table)

expect(db.tables.len()).to_equal(5)

# Verify all tables accessible
for i in 0..5:
    val table_opt = db.get_table("table_{i}")
    expect(table_opt.?).to_equal(true)
```

</details>

#### preserves table order

1. var db = SdnDatabase

2. db set table
   - Expected: db.get_table("first").? is true
   - Expected: db.get_table("second").? is true
   - Expected: db.get_table("third").? is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_table_order.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)

val names = ["first", "second", "third"]
for name in names:
    val table = SdnTable(name: name, columns: ["id"], rows: [], index: {})
    db.set_table(name, table)

# Tables should be accessible in any order
expect(db.get_table("first").?).to_equal(true)
expect(db.get_table("second").?).to_equal(true)
expect(db.get_table("third").?).to_equal(true)
```

</details>

### Database Integration

#### combines interner with database

1. var db = SdnDatabase

2. var interner = StringInterner

3. var table = SdnTable

4. var row = SdnRow

5. row set

6. row set

7. table add row

8. db set table
   - Expected: saved_table.rows.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_interner_db.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)
var interner = StringInterner(strings: {}, reverse: {}, next_id: 0)

# Intern column names
val col_id = interner.intern("id")
val col_name = interner.intern("name")

# Create table with interned names
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

# Add row
var row = SdnRow(fields: {})
row.set(interner.lookup(col_id)?, "user_1")
row.set(interner.lookup(col_name)?, "Alice")
table.add_row(row)

db.set_table("users", table)

# Verify
val saved_table = db.get_table("users")?
expect(saved_table.rows.len()).to_equal(1)
```

</details>

#### handles large number of rows efficiently

1. var db = SdnDatabase

2. var table = SdnTable

3. var row = SdnRow

4. row set

5. row set

6. table add row

7. db set table
   - Expected: result.rows.len() equals `1000`
   - Expected: row_500.get("data")? equals `data_500`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "/tmp/test_large_db.sdn", tables: {}, interner: StringInterner(strings: {}, reverse: {}, next_id: 0), modified: false)
var table = SdnTable(name: "large", columns: ["id", "data"], rows: [], index: {})

# Add 1000 rows
for i in 0..1000:
    var row = SdnRow(fields: {})
    row.set("id", "row_{i}")
    row.set("data", "data_{i}")
    table.add_row(row)

db.set_table("large", table)

# Verify
val result = db.get_table("large")?
expect(result.rows.len()).to_equal(1000)

# Spot check
val row_500 = result.get_row("row_500")?
expect(row_500.get("data")?).to_equal("data_500")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StringInterner
- SdnRow
- SdnTable
- SdnDatabase
- Database Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
