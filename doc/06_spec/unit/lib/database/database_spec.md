# Database Specification

> Tests covering StringInterner, SdnRow, SdnTable, SdnDatabase, BugDatabase.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Specification

## Scenarios

### StringInterner

#### creates empty interner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty interner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty interner")
val interner = StringInterner.empty()
check(interner.next_id.value == 0)
check(interner.str_to_id.keys().len() == 0)
```

</details>

#### interns strings with unique IDs

- interns strings with unique IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interns strings with unique IDs")
var interner = StringInterner.empty()
val id1 = interner.intern("hello")
val id2 = interner.intern("world")
val id3 = interner.intern("hello")  # Same string

check(id1 == 0)
check(id2 == 1)
check(id3 == 0)  # Reuses ID
```

</details>

#### resolves IDs to strings

- resolves IDs to strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves IDs to strings")
var interner = StringInterner.empty()
val id = interner.intern("test")
val resolved = interner.get(id)?

check(resolved == "test")
```

</details>

#### returns None for invalid ID

- returns None for invalid ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for invalid ID")
val interner = StringInterner.empty()
val resolved = interner.get(999)

check(not resolved.?)
```

</details>

#### exports to SDN table

- exports to SDN table


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports to SDN table")
var interner = StringInterner.empty()
interner.intern("foo")
interner.intern("bar")

val table = interner.to_sdn()
check(table.name == "strings")
check(table.rows.len() == 2)
```

</details>

#### loads from SDN table

- loads from SDN table


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads from SDN table")
# Create table
val table = SdnTable(name: "strings", columns: ["id", "value"], rows: [], index: {})
var row1 = SdnRow(fields: {}, _version: 0)
row1.set("id", "0")
row1.set("value", "test1")
table.add_row(row1)

var row2 = SdnRow(fields: {}, _version: 0)
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

- creates empty row


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty row")
val row = SdnRow(fields: {}, _version: 0)
check(row.fields.keys().len() == 0)
```

</details>

#### sets and gets field values

- sets and gets field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets and gets field values")
var row = SdnRow(fields: {}, _version: 0)
row.set("name", "Alice")
row.set("age", "30")

check(row.get("name")? == "Alice")
check(row.get("age")? == "30")
```

</details>

#### returns None for missing field

- returns None for missing field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None for missing field")
val row = SdnRow(fields: {}, _version: 0)
check(not row.get("missing").?)
```

</details>

#### parses i64 fields

- parses i64 fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses i64 fields")
var row = SdnRow(fields: {}, _version: 0)
row.set("count", "42")

check(row.get_i64("count")? == 42)
```

</details>

#### parses bool fields

- parses bool fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bool fields")
var row = SdnRow(fields: {}, _version: 0)
row.set("active", "true")
row.set("disabled", "false")

check(row.get_bool("active")? == true)
check(row.get_bool("disabled")? == false)
```

</details>

#### checks if has column

- checks if has column


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if has column")
var row = SdnRow(fields: {}, _version: 0)
row.set("name", "Bob")

check(row.has_column("name"))
check(not row.has_column("age"))
```

</details>

### SdnTable

#### creates new table

- creates new table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new table")
val table = SdnTable(name: "users", columns: ["id", "name", "email"], rows: [], index: {})

check(table.name == "users")
check(table.columns.len() == 3)
check(table.rows.len() == 0)
```

</details>

#### adds rows

- adds rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds rows")
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
row.set("id", "1")
row.set("name", "Alice")

table.add_row(row)
check(table.rows.len() == 1)
```

</details>

#### indexes rows by primary key

- indexes rows by primary key


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indexes rows by primary key")
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
row.set("id", "user_1")
row.set("name", "Alice")
table.add_row(row)

val found = table.get_row("user_1")?
check(found.get("name")? == "Alice")
```

</details>

#### updates row by key

- updates row by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates row by key")
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row1 = SdnRow(fields: {}, _version: 0)
row1.set("id", "user_1")
row1.set("name", "Alice")
table.add_row(row1)

var row2 = SdnRow(fields: {}, _version: 0)
row2.set("id", "user_1")
row2.set("name", "Bob")
table.update_row("user_1", row2)

val found = table.get_row("user_1")?
check(found.get("name")? == "Bob")
```

</details>

#### soft deletes rows

- soft deletes rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("soft deletes rows")
var table = SdnTable(name: "users", columns: ["id", "name", "valid"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
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

- exports to SDN format


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports to SDN format")
var table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})

var row = SdnRow(fields: {}, _version: 0)
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

- creates new database


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new database")
val db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

check(db.path == "test_db.sdn")
check(db.tables.len() == 0)
```

</details>

#### adds and retrieves tables

- adds and retrieves tables


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds and retrieves tables")
var db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val table = SdnTable(name: "users", columns: ["id", "name"], rows: [], index: {})
db.set_table("users", table)

val retrieved = db.get_table("users")?
check(retrieved.name == "users")
```

</details>

#### interns strings

- interns strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interns strings")
var db = SdnDatabase(path: "test_db.sdn", tables: {}, interner: StringInterner.empty(), modified: false)

val id1 = db.intern("hello")
val id2 = db.intern("hello")

check(id1 == id2)
check(db.resolve(id1)? == "hello")
```

</details>

### BugDatabase

#### creates new bug database

- creates new bug database


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new bug database")
val bugdb = create_bug_database("/tmp/test_bugdb.sdn")

check(bugdb.db.tables.has("bugs"))
check(bugdb.db.tables.has("bug_descriptions"))
check(bugdb.db.tables.has("bug_fix_strategies"))
check(bugdb.db.tables.has("bug_investigation_logs"))
```

</details>

#### adds and retrieves bugs

- adds and retrieves bugs


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds and retrieves bugs")
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

- queries bugs by status


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries bugs by status")

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

- queries critical bugs


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries critical bugs")

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

- generates statistics


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates statistics")

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

- validates test links


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates test links")

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
| Source | `test/unit/lib/database/database_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StringInterner, SdnRow, SdnTable, SdnDatabase, BugDatabase.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26b4cac56528193c5798e535933b08a0b169195890999afc04fc81c965df99cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26b4cac56528193c5798e535933b08a0b169195890999afc04fc81c965df99cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26b4cac56528193c5798e535933b08a0b169195890999afc04fc81c965df99cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/database/database_spec.spl
mirror: doc/06_spec/unit/lib/database/database_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/database/database_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/database/database_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/database/database_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty interner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/database/database_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interns strings with unique IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/database/database_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves IDs to strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
