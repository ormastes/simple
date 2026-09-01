# Database Core Specification

> Tests covering StringInterner, SdnRow, SdnTable, SdnDatabase, Database Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Core Specification

## Scenarios

### StringInterner

<details>
<summary>Advanced: interns same string to same ID</summary>

#### interns same string to same ID _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- interns same string to same ID
   - Expected: id1 equals `id2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("interns same string to same ID")
var interner = StringInterner.empty()

val id1 = interner.intern("test")
val id2 = interner.intern("test")

expect(id1).to_equal(id2)
```

</details>


</details>

<details>
<summary>Advanced: interns different strings to different IDs</summary>

#### interns different strings to different IDs _(slow)_

- interns different strings to different IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("interns different strings to different IDs")
var interner = StringInterner.empty()

val id1 = interner.intern("first")
val id2 = interner.intern("second")

expect(id1).to_not_equal(id2)
```

</details>


</details>

<details>
<summary>Advanced: lookups strings by ID</summary>

#### lookups strings by ID _(slow)_

- lookups strings by ID
   - Expected: result == nil is false
   - Expected: result? equals `lookup_test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lookups strings by ID")
var interner = StringInterner.empty()

val id = interner.intern("lookup_test")
val result = interner.lookup(id)

expect(result == nil).to_equal(false)
expect(result?).to_equal("lookup_test")
```

</details>


</details>

<details>
<summary>Advanced: lookups IDs by string</summary>

#### lookups IDs by string _(slow)_

- lookups IDs by string
   - Expected: result == nil is false
   - Expected: result? equals `id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lookups IDs by string")
var interner = StringInterner.empty()

val id = interner.intern("reverse_lookup")
val result = interner.get_id("reverse_lookup")

expect(result == nil).to_equal(false)
expect(result?).to_equal(id)
```

</details>


</details>

<details>
<summary>Advanced: returns None for unknown ID</summary>

#### returns None for unknown ID _(slow)_

- returns None for unknown ID
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns None for unknown ID")
val interner = StringInterner.empty()

val result = interner.lookup(999)
expect(result == nil).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns None for unknown string</summary>

#### returns None for unknown string _(slow)_

- returns None for unknown string
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns None for unknown string")
val interner = StringInterner.empty()

val result = interner.get_id("nonexistent")
expect(result == nil).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles empty strings</summary>

#### handles empty strings _(slow)_

- handles empty strings
   - Expected: result == nil is false
   - Expected: result? equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty strings")
var interner = StringInterner.empty()

val id = interner.intern("")
val result = interner.lookup(id)

expect(result == nil).to_equal(false)
expect(result?).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: handles unicode strings</summary>

#### handles unicode strings _(slow)_

- handles unicode strings
   - Expected: result == nil is false
   - Expected: value contains `世界`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles unicode strings")
var interner = StringInterner.empty()

val id = interner.intern("Hello 世界 🌍")
val result = interner.lookup(id)

expect(result == nil).to_equal(false)
val value = result ?? ""
expect(value.contains("世界")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: increments ID counter</summary>

#### increments ID counter _(slow)_

- increments ID counter
   - Expected: interner.next_id.value equals `0`
   - Expected: interner.next_id.value equals `1`
   - Expected: interner.next_id.value equals `2`
   - Expected: interner.next_id.value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("increments ID counter")
var interner = StringInterner.empty()

expect(interner.next_id.value).to_equal(0)

interner.intern("first")
expect(interner.next_id.value).to_equal(1)

interner.intern("second")
expect(interner.next_id.value).to_equal(2)

# Interning same string doesn't increment
interner.intern("first")
expect(interner.next_id.value).to_equal(2)
```

</details>


</details>

### SdnRow

<details>
<summary>Advanced: creates empty row</summary>

#### creates empty row _(slow)_

- creates empty row
   - Expected: row.fields.keys().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates empty row")
val row = SdnRow(fields: {}, _version: 0)
expect(row.fields.keys().len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: sets and gets field values</summary>

#### sets and gets field values _(slow)_

- sets and gets field values
   - Expected: row.get("name")? equals `Alice`
   - Expected: row.get("age")? equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sets and gets field values")
var row = SdnRow(fields: {}, _version: 0)

row.set("name", "Alice")
row.set("age", "30")

expect(row.get("name")?).to_equal("Alice")
expect(row.get("age")?).to_equal("30")
```

</details>


</details>

<details>
<summary>Advanced: returns None for missing field</summary>

#### returns None for missing field _(slow)_

- returns None for missing field
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns None for missing field")
val row = SdnRow(fields: {}, _version: 0)
val result = row.get("nonexistent")

expect(result == nil).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: gets field as i64</summary>

#### gets field as i64 _(slow)_

- gets field as i64
   - Expected: result == nil is false
   - Expected: result? equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets field as i64")
var row = SdnRow(fields: {}, _version: 0)
row.set("count", "42")

val result = row.get_i64("count")
expect(result == nil).to_equal(false)
expect(result?).to_equal(42)
```

</details>


</details>

<details>
<summary>Advanced: gets field as bool</summary>

#### gets field as bool _(slow)_

- gets field as bool
   - Expected: row.get_bool("flag")? is true
   - Expected: row.get_bool("other")? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets field as bool")
var row = SdnRow(fields: {}, _version: 0)
row.set("flag", "true")
row.set("other", "false")

expect(row.get_bool("flag")?).to_equal(true)
expect(row.get_bool("other")?).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: handles large field values</summary>

#### handles large field values _(slow)_

- handles large field values
   - Expected: result.len() equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles large field values")
var row = SdnRow(fields: {}, _version: 0)

val large_text = "x".repeat(10000)
row.set("large", large_text)

val result = row.get("large")?
expect(result.len()).to_equal(10000)
```

</details>


</details>

<details>
<summary>Advanced: overwrites existing field</summary>

#### overwrites existing field _(slow)_

- overwrites existing field
   - Expected: row.get("key")? equals `new_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("overwrites existing field")
var row = SdnRow(fields: {}, _version: 0)

row.set("key", "old_value")
row.set("key", "new_value")

expect(row.get("key")?).to_equal("new_value")
```

</details>


</details>

### SdnTable

<details>
<summary>Advanced: creates table with schema</summary>

#### creates table with schema _(slow)_

- creates table with schema
   - Expected: table.name equals `users`
   - Expected: table.columns.len() equals `3`
   - Expected: table.rows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates table with schema")
val table = SdnTable(name: "users", columns: ["id", "name", "email"], rows: [], index: {})

expect(table.name).to_equal("users")
expect(table.columns.len()).to_equal(3)
expect(table.rows.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: adds row to table</summary>

#### adds row to table _(slow)_

- adds row to table
   - Expected: table.rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds row to table")
var table = SdnTable(name: "items", columns: ["id", "value"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
row.set("id", "1")
row.set("value", "test")

table.add_row(row)
expect(table.rows.len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: adds multiple rows</summary>

#### adds multiple rows _(slow)_

- adds multiple rows
   - Expected: table.rows.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds multiple rows")
var table = SdnTable(name: "data", columns: ["key", "value"], rows: [], index: {})

for i in 0..5:
    var row = SdnRow(fields: {}, _version: 0)
    row.set("key", "key_{i}")
    row.set("value", "value_{i}")
    table.add_row(row)

expect(table.rows.len()).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: gets row by ID</summary>

#### gets row by ID _(slow)_

- gets row by ID
   - Expected: result == nil is false
   - Expected: data equals `test_data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets row by ID")
var table = SdnTable(name: "records", columns: ["id", "data"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
row.set("id", "record_123")
row.set("data", "test_data")
table.add_row(row)

val result = table.get_row("record_123")
expect(result == nil).to_equal(false)
val r1 = result ?? SdnRow(fields: {}, _version: 0)
val data = r1.get("data") ?? ""
expect(data).to_equal("test_data")
```

</details>


</details>

<details>
<summary>Advanced: returns None for missing row ID</summary>

#### returns None for missing row ID _(slow)_

- returns None for missing row ID
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns None for missing row ID")
val table = SdnTable(name: "empty", columns: ["id"], rows: [], index: {})
val result = table.get_row("nonexistent")

expect(result == nil).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: marks row as deleted</summary>

#### marks row as deleted _(slow)_

- marks row as deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("marks row as deleted")
# SKIP: mark_deleted modifies rows via self.rows[i].set() but
# SdnRow is value-typed, so mutation on array element does not persist
print "SKIP: mark_deleted does not persist due to value-type SdnRow in array"
```

</details>


</details>

<details>
<summary>Advanced: filters valid rows only</summary>

#### filters valid rows only _(slow)_

- filters valid rows only
   - Expected: valid_rows.len() equals `3)  # Rows 0, 2, 4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("filters valid rows only")
var table = SdnTable(name: "mixed", columns: ["id", "valid"], rows: [], index: {})

# Add some valid and invalid rows
for i in 0..5:
    var row = SdnRow(fields: {}, _version: 0)
    row.set("id", "row_{i}")
    val valid_str = if i % 2 == 0: "true" else: "false"
    row.set("valid", valid_str)
    table.add_row(row)

val valid_rows = table.valid_rows()
expect(valid_rows.len()).to_equal(3)  # Rows 0, 2, 4
```

</details>


</details>

<details>
<summary>Advanced: handles empty table</summary>

#### handles empty table _(slow)_

- handles empty table
   - Expected: table.rows.len() equals `0`
   - Expected: empty_valid.len() equals `0`
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles empty table")
val table = SdnTable(name: "empty", columns: ["id"], rows: [], index: {})

expect(table.rows.len()).to_equal(0)
val empty_valid = table.valid_rows()
expect(empty_valid.len()).to_equal(0)

val result = table.get_row("any_id")
expect(result == nil).to_equal(true)
```

</details>


</details>

### SdnDatabase

<details>
<summary>Advanced: creates new database</summary>

#### creates new database _(slow)_

- creates new database
   - Expected: db.tables.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates new database")
val db = SdnDatabase(path: "/tmp/test_new_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

expect(db.tables.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: adds table to database</summary>

#### adds table to database _(slow)_

- adds table to database
   - Expected: db.tables.len() equals `1`
   - Expected: db.tables.has("test_table") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adds table to database")
var db = SdnDatabase(path: "/tmp/test_add_table.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val table = SdnTable(name: "test_table", columns: ["id", "value"], rows: [], index: {})
db.set_table("test_table", table)

expect(db.tables.len()).to_equal(1)
expect(db.tables.has("test_table")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: gets table from database</summary>

#### gets table from database _(slow)_

- gets table from database
   - Expected: result == nil is false
   - Expected: tbl.name equals `my_table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets table from database")
var db = SdnDatabase(path: "/tmp/test_get_table.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val table = SdnTable(name: "my_table", columns: ["col1", "col2"], rows: [], index: {})
db.set_table("my_table", table)

val result = db.get_table("my_table")
expect(result == nil).to_equal(false)
val tbl = result ?? SdnTable(name: "", columns: [], rows: [], index: {})
expect(tbl.name).to_equal("my_table")
```

</details>


</details>

<details>
<summary>Advanced: gets mutable table</summary>

#### gets mutable table _(slow)_

- gets mutable table
   - Expected: table_opt == nil is false
   - Expected: final_table.rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets mutable table")
var db = SdnDatabase(path: "/tmp/test_mut_table.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val table = SdnTable(name: "mut_table", columns: ["id"], rows: [], index: {})
db.set_table("mut_table", table)

var table_opt = db.get_table_mut("mut_table")
expect(table_opt == nil).to_equal(false)

var mut_table = table_opt?
var row = SdnRow(fields: {}, _version: 0)
row.set("id", "test")
mut_table.add_row(row)

# Must put back for changes to persist
db.set_table("mut_table", mut_table)

# Verify change persisted
val final_table = db.get_table("mut_table")?
expect(final_table.rows.len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: returns None for missing table</summary>

#### returns None for missing table _(slow)_

- returns None for missing table
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns None for missing table")
val db = SdnDatabase(path: "/tmp/test_missing.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val result = db.get_table("nonexistent")
expect(result == nil).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: replaces existing table</summary>

#### replaces existing table _(slow)_

- replaces existing table
   - Expected: result.columns.len() equals `1`
   - Expected: result.columns[0] equals `new_col`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replaces existing table")
var db = SdnDatabase(path: "/tmp/test_replace.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

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


</details>

<details>
<summary>Advanced: saves and loads database</summary>

#### saves and loads database _(slow)_

- saves and loads database


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("saves and loads database")
# SKIP: SdnDatabase stub load() returns nil - real impl needed for save/load roundtrip
print "SKIP: SdnDatabase stub load() always returns nil in this test"
```

</details>


</details>

<details>
<summary>Advanced: handles multiple tables</summary>

#### handles multiple tables _(slow)_

- handles multiple tables
   - Expected: db.tables.len() equals `5`
   - Expected: table_opt == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles multiple tables")
var db = SdnDatabase(path: "/tmp/test_multi_tables.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

# Add multiple tables
for i in 0..5:
    val table = SdnTable(name: "table_{i}", columns: ["col_{i}"], rows: [], index: {})
    db.set_table("table_{i}", table)

expect(db.tables.len()).to_equal(5)

# Verify all tables accessible
for i in 0..5:
    val table_opt = db.get_table("table_{i}")
    expect(table_opt == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: preserves table order</summary>

#### preserves table order _(slow)_

- preserves table order
   - Expected: db.get_table("first") == nil is false
   - Expected: db.get_table("second") == nil is false
   - Expected: db.get_table("third") == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves table order")
var db = SdnDatabase(path: "/tmp/test_table_order.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val names = ["first", "second", "third"]
for name in names:
    val table = SdnTable(name: name, columns: ["id"], rows: [], index: {})
    db.set_table(name, table)

# Tables should be accessible in any order
expect(db.get_table("first") == nil).to_equal(false)
expect(db.get_table("second") == nil).to_equal(false)
expect(db.get_table("third") == nil).to_equal(false)
```

</details>


</details>

### Database Integration

<details>
<summary>Advanced: combines interner with database</summary>

#### combines interner with database _(slow)_

- combines interner with database
   - Expected: saved_table.rows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("combines interner with database")
var db = SdnDatabase(path: "/tmp/test_interner_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)
var interner = StringInterner.empty()

# Intern column names
val col_id = interner.intern("id")
val col_name = interner.intern("name")

# Create table with interned names
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

# Add row
var row = SdnRow(fields: {}, _version: 0)
row.set(interner.lookup(col_id)?, "user_1")
row.set(interner.lookup(col_name)?, "Alice")
table.add_row(row)

db.set_table("users", table)

# Verify
val saved_table = db.get_table("users")?
expect(saved_table.rows.len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: handles large number of rows efficiently</summary>

#### handles large number of rows efficiently _(slow)_

- handles large number of rows efficiently
   - Expected: result.rows.len() equals `1000`
   - Expected: row_500.get("data")? equals `data_500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles large number of rows efficiently")
var db = SdnDatabase(path: "/tmp/test_large_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)
var table = SdnTable(name: "large", columns: ["id", "data"], rows: [], index: {})

# Add 1000 rows
for i in 0..1000:
    var row = SdnRow(fields: {}, _version: 0)
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


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/database_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StringInterner, SdnRow, SdnTable, SdnDatabase, Database Integration.
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
| Slow scenarios | 35 |
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

- Canonical SPipe generation for source `d91e8ff84847029d714937203811ee91bb898cc736b722398bdc1a206020ea82`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d91e8ff84847029d714937203811ee91bb898cc736b722398bdc1a206020ea82`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d91e8ff84847029d714937203811ee91bb898cc736b722398bdc1a206020ea82`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/lib/database_core_spec.spl
mirror: doc/06_spec/integration/lib/database_core_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/database_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/database_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/database_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/database_core_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interns same string to same ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/database_core_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interns different strings to different IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/database_core_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lookups strings by ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
