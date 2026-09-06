# Database System Specification

> Tests covering Database system production workflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database System Specification

## Scenarios

### Database system production workflow

#### saves and reloads an SDN database through the production API

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("round_trip")
_cleanup(path)
```

</details>

#### persists an empty terminal field without trailing whitespace and reloads it

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("empty_terminal_field")
_cleanup(path)

var db = SdnDatabase.new(path)
var table = SdnTable.new("notes", ["id", "content"])
var row = SdnRow.empty()
row.set("id", "note-1")
row.set("content", "")
table.add_row(row)
db.set_table("notes", table)

expect(db.save()).to_equal(true)
val persisted = rt_file_read_text(path) ?? ""
expect(persisted.contains("note-1, \n")).to_equal(false)
expect(persisted.contains("note-1, \"\"\n")).to_equal(true)
expect(persisted.ends_with("\n\n")).to_equal(false)
val loaded = load_sdn_database(path)?
expect(loaded.get_table("notes")?.get_row("note-1")?.get("content")?).to_equal("")

_cleanup(path)

var db = _database_with_items(path)
expect(db.save()).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)

val loaded_opt = load_sdn_database(path)
expect(loaded_opt != nil).to_equal(true)
val loaded = loaded_opt?
val table_opt = loaded.get_table("items")
expect(table_opt != nil).to_equal(true)
val table = table_opt?
expect(table.rows.len()).to_equal(3)
expect(table.get_row("item-1").unwrap().get("name").unwrap()).to_equal("alpha")

_cleanup(path)
```

</details>

#### updates and soft-deletes rows while keeping indexes usable

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("mutations")
_cleanup(path)

var db = _database_with_items(path)
var table = db.get_table("items")?
var updated = _item("item-2", "beta-updated", "open", "true")
expect(table.update_row("item-2", updated)).to_equal(true)
expect(table.mark_deleted("item-1")).to_equal(true)
db.set_table("items", table)

expect(db.save()).to_equal(true)
val loaded = load_sdn_database(path)?
val loaded_table = loaded.get_table("items")?
expect(loaded_table.get_row("item-2").unwrap().get("name").unwrap()).to_equal("beta-updated")
expect(loaded_table.get_row("item-1").unwrap().get("valid").unwrap()).to_equal("false")
expect(loaded_table.valid_rows().len()).to_equal(1)

_cleanup(path)
```

</details>

#### queries saved production rows with filters and ordering

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("query")
_cleanup(path)

var db = _database_with_items(path)
expect(db.save()).to_equal(true)
val loaded = load_sdn_database(path)?
val query_opt = query_table(loaded, "items")
expect(query_opt != nil).to_equal(true)
var query = query_opt?
val rows = query.filter_by("status", CompareOp.Eq, "open")
    .filter_by("valid", CompareOp.Eq, "true")
    .order_by("name", false)
    .execute()

expect(rows.len()).to_equal(1)
expect(rows[0].get("id").unwrap()).to_equal("item-1")

_cleanup(path)
```

</details>

#### rejects malformed SDN table imports without mutating the database

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("malformed")
_cleanup(path)

var db = SdnDatabase.new(path)
expect(db.import_table_sdn("not a table")).to_equal(false)
expect(db.get_table("not") != nil).to_equal(false)
expect(db.modified).to_equal(false)

_cleanup(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/database/database_system_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Database system production workflow.
- Database system production workflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
