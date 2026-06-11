# Database Specification

> 1. check

<!-- sdn-diagram:id=database_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Specification

## Scenarios

### StringInterner

#### creates empty interner

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interner = StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)
check(interner.next_id == 0)
check(interner.str_to_id.len() == 0)
```

</details>

#### interns strings with unique IDs

1. var interner = StringInterner
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)
val id1 = interner.intern("hello")
val id2 = interner.intern("world")
val id3 = interner.intern("hello")  # Same string

check(id1 == 0)
check(id2 == 1)
check(id3 == 0)  # Reuses ID
```

</details>

#### resolves IDs to strings

1. var interner = StringInterner
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)
val id = interner.intern("test")
val resolved = interner.get(id)?

check(resolved == "test")
```

</details>

#### returns None for invalid ID

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interner = StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)
val resolved = interner.get(999)

check(not resolved.?)
```

</details>

#### exports to SDN table

1. var interner = StringInterner
2. interner intern
3. interner intern
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var interner = StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0)
interner.intern("foo")
interner.intern("bar")

val table = interner.to_sdn()
check(table.name == "strings")
check(table.rows.len() == 2)
```

</details>

#### loads from SDN table

1. var row1 = SdnRow
2. row1 set
3. row1 set
4. table add row
5. var row2 = SdnRow
6. row2 set
7. row2 set
8. table add row
9. check
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create table
val table = SdnTable(name: "strings", columns: ["id", "value"], rows: [], index: {})
var row1 = SdnRow(fields: {})
row1.set("id", "0")
row1.set("value", "test1")
table.add_row(row1)

var row2 = SdnRow(fields: {})
row2.set("id", "1")
row2.set("value", "test2")
table.add_row(row2)

# Load interner
val interner = StringInterner.from_sdn(table)
check(interner.get(0)? == "test1")
check(interner.get(1)? == "test2")
```

</details>

### SdnRow

#### creates empty row

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = SdnRow(fields: {})
check(row.fields.len() == 0)
```

</details>

#### sets and gets field values

1. var row = SdnRow
2. row set
3. row set
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("name", "Alice")
row.set("age", "30")

check(row.get("name")? == "Alice")
check(row.get("age")? == "30")
```

</details>

#### returns None for missing field

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = SdnRow(fields: {})
check(not row.get("missing").?)
```

</details>

#### parses i64 fields

1. var row = SdnRow
2. row set
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("count", "42")

check(row.get_i64("count")? == 42)
```

</details>

#### parses bool fields

1. var row = SdnRow
2. row set
3. row set
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("active", "true")
row.set("disabled", "false")

check(row.get_bool("active")? == true)
check(row.get_bool("disabled")? == false)
```

</details>

#### checks if has column

1. var row = SdnRow
2. row set
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var row = SdnRow(fields: {})
row.set("name", "Bob")

check(row.has_column("name"))
check(not row.has_column("age"))
```

</details>

### SdnTable

#### creates new table

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = SdnTable(name: "users", columns: ["id", "name", "email"], rows: [], index: {})

check(table.name == "users")
check(table.columns.len() == 3)
check(table.rows.len() == 0)
```

</details>

#### adds rows

1. var table = SdnTable
2. var row = SdnRow
3. row set
4. row set
5. table add row
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "1")
row.set("name", "Alice")

table.add_row(row)
check(table.rows.len() == 1)
```

</details>

#### indexes rows by primary key

1. var table = SdnTable
2. var row = SdnRow
3. row set
4. row set
5. table add row
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "user_1")
row.set("name", "Alice")
table.add_row(row)

val found = table.get_row("user_1")?
check(found.get("name")? == "Alice")
```

</details>

#### updates row by key

1. var table = SdnTable
2. var row1 = SdnRow
3. row1 set
4. row1 set
5. table add row
6. var row2 = SdnRow
7. row2 set
8. row2 set
9. table update row
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row1 = SdnRow(fields: {})
row1.set("id", "user_1")
row1.set("name", "Alice")
table.add_row(row1)

var row2 = SdnRow(fields: {})
row2.set("id", "user_1")
row2.set("name", "Bob")
table.update_row("user_1", row2)

val found = table.get_row("user_1")?
check(found.get("name")? == "Bob")
```

</details>

#### soft deletes rows

1. var table = SdnTable
2. var row = SdnRow
3. row set
4. row set
5. row set
6. table add row
7. table mark deleted
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "users", columns: ["id", "name", "valid"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "user_1")
row.set("name", "Alice")
row.set("valid", "true")
table.add_row(row)

table.mark_deleted("user_1")

val all_rows = table.rows
val valid_rows = table.valid_rows()

check(all_rows.len() == 1)
check(valid_rows.len() == 0)
```

</details>

#### exports to SDN format

1. var table = SdnTable
2. var row = SdnRow
3. row set
4. row set
5. table add row
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {})
row.set("id", "1")
row.set("name", "Alice")
table.add_row(row)

val sdn = table.to_sdn()
check(sdn.contains("users |id, name|"))
check(sdn.contains("1, Alice"))
```

</details>

### SdnDatabase

#### creates new database

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0), modified: false)

check(db.path == "test_db.sdn")
check(db.tables.len() == 0)
```

</details>

#### adds and retrieves tables

1. var db = SdnDatabase
2. db set table
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0), modified: false)

val table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})
db.set_table("users", table)

val retrieved = db.get_table("users")?
check(retrieved.name == "users")
```

</details>

#### interns strings

1. var db = SdnDatabase
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner(str_to_id: {}, id_to_str: {}, next_id: 0), modified: false)

val id1 = db.intern("hello")
val id2 = db.intern("hello")

check(id1 == id2)
check(db.resolve(id1)? == "hello")
```

</details>

### BugDatabase

#### creates new bug database

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bugdb = create_bug_database("/tmp/test_bugdb.sdn")

check(bugdb.db.tables.has("bugs"))
check(bugdb.db.tables.has("bug_descriptions"))
check(bugdb.db.tables.has("bug_fix_strategies"))
check(bugdb.db.tables.has("bug_investigation_logs"))
```

</details>

#### adds and retrieves bugs

1. var bugdb = create bug database
2. severity: BugSeverity P1
3. status: BugStatus Open
4. check
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bugdb = create_bug_database("/tmp/test_bugdb.sdn")

val bug = Bug(
    id: "test_001",
    severity: BugSeverity.P1(),
    status: BugStatus.Open(),
    title: "Test bug",
    description: ["Line 1", "Line 2"],
    file: "test.spl",
    line: 42,
    reproducible_by: "test_case",
    fix_strategy: ["Fix step 1"],
    investigation_log: [],
    created_at: "2026-02-05T10:00:00",
    updated_at: "2026-02-05T10:00:00",
    valid: true
)

val added = bugdb.add_bug(bug)
check(added)

# Check we can get all bugs
val all_bugs = bugdb.all_bugs()
check(all_bugs.len() == 1)

val first_bug = all_bugs[0]
check(first_bug.title == "Test bug")
check(first_bug.severity == BugSeverity.P1())
check(first_bug.description.len() == 2)
```

</details>

#### queries bugs by status

1. var bugdb = create bug database
2. severity: BugSeverity P1
3. status: BugStatus Open
4. severity: BugSeverity P2
5. status: BugStatus Fixed
6. bugdb add bug
7. bugdb add bug
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var bugdb = create_bug_database("/tmp/test.sdn")

val bug1 = Bug(
    id: "bug_001",
    severity: BugSeverity.P1(),
    status: BugStatus.Open(),
    title: "Bug 1",
    description: [],
    file: "test.spl",
    line: 1,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val bug2 = Bug(
    id: "bug_002",
    severity: BugSeverity.P2(),
    status: BugStatus.Fixed(),
    title: "Bug 2",
    description: [],
    file: "test.spl",
    line: 2,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(bug1)
bugdb.add_bug(bug2)

val open_bugs = bugdb.bugs_by_status(BugStatus.Open())
val fixed_bugs = bugdb.bugs_by_status(BugStatus.Fixed())

check(open_bugs.len() == 1)
check(fixed_bugs.len() == 1)
```

</details>

#### queries critical bugs

1. var bugdb = create bug database
2. severity: BugSeverity P0
3. status: BugStatus Open
4. severity: BugSeverity P2
5. status: BugStatus Open
6. bugdb add bug
7. bugdb add bug
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var bugdb = create_bug_database("/tmp/test.sdn")

val p0_bug = Bug(
    id: "bug_p0",
    severity: BugSeverity.P0(),
    status: BugStatus.Open(),
    title: "Critical",
    description: [],
    file: "test.spl",
    line: 1,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val p2_bug = Bug(
    id: "bug_p2",
    severity: BugSeverity.P2(),
    status: BugStatus.Open(),
    title: "Low",
    description: [],
    file: "test.spl",
    line: 2,
    reproducible_by: "test",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(p0_bug)
bugdb.add_bug(p2_bug)

val critical = bugdb.critical_bugs()
check(critical.len() == 1)
```

</details>

#### generates statistics

1. var bugdb = create bug database
2. BugSeverity P1
3. BugSeverity P2
4. BugStatus Open
5. BugStatus Fixed
6. bugdb add bug
7. check
8. check
9. check
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var bugdb = create_bug_database("/tmp/test.sdn")

# Add various bugs
for i in 0..5:
    val severity = if i < 2:
        BugSeverity.P1()
    else:
        BugSeverity.P2()

    val status = if i < 3:
        BugStatus.Open()
    else:
        BugStatus.Fixed()

    val bug = Bug(
        id: "bug_{i}",
        severity: severity,
        status: status,
        title: "Bug {i}",
        description: [],
        file: "test.spl",
        line: i,
        reproducible_by: "test",
        fix_strategy: [],
        investigation_log: [],
        created_at: "2026-02-05",
        updated_at: "2026-02-05",
        valid: true
    )
    bugdb.add_bug(bug)

val stats = bugdb.stats()
check(stats["total"] == 5)
check(stats["open"] == 3)
check(stats["fixed"] == 2)
check(stats["p1"] == 2)
```

</details>

#### validates test links

1. var bugdb = create bug database
2. severity: BugSeverity P1
3. status: BugStatus Open
4. severity: BugSeverity P1
5. status: BugStatus Open
6. bugdb add bug
7. bugdb add bug
8. check
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var bugdb = create_bug_database("/tmp/test.sdn")

val bug_with_test = Bug(
    id: "bug_001",
    severity: BugSeverity.P1(),
    status: BugStatus.Open(),
    title: "With test",
    description: [],
    file: "test.spl",
    line: 1,
    reproducible_by: "test_case",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

val bug_no_test = Bug(
    id: "bug_002",
    severity: BugSeverity.P1(),
    status: BugStatus.Open(),
    title: "No test",
    description: [],
    file: "test.spl",
    line: 2,
    reproducible_by: "",
    fix_strategy: [],
    investigation_log: [],
    created_at: "2026-02-05",
    updated_at: "2026-02-05",
    valid: true
)

bugdb.add_bug(bug_with_test)
bugdb.add_bug(bug_no_test)

val errors = bugdb.validate_test_links()
check(errors.len() == 1)
check(errors[0].contains("bug_002"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StringInterner
- SdnRow
- SdnTable
- SdnDatabase
- BugDatabase

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
