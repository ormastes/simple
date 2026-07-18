# Database System Specification

> 1.  cleanup

<!-- sdn-diagram:id=database_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database System Specification

## Scenarios

### Database system production workflow

#### saves and reloads an SDN database through the production API

1.  cleanup

2. var db =  database with items
   - Expected: db.save() is true
   - Expected: rt_file_exists(path) is true
   - Expected: loaded_opt.? is true
   - Expected: table_opt.? is true
   - Expected: table.rows.len() equals `3`
   - Expected: table.get_row("item-1").unwrap().get("name").unwrap() equals `alpha`

3.  cleanup


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("round_trip")
_cleanup(path)

var db = _database_with_items(path)
expect(db.save()).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)

val loaded_opt = load_sdn_database(path)
expect(loaded_opt.?).to_equal(true)
val loaded = loaded_opt?
val table_opt = loaded.get_table("items")
expect(table_opt.?).to_equal(true)
val table = table_opt?
expect(table.rows.len()).to_equal(3)
expect(table.get_row("item-1").unwrap().get("name").unwrap()).to_equal("alpha")

_cleanup(path)
```

</details>

#### updates and soft-deletes rows while keeping indexes usable

1.  cleanup

2. var db =  database with items

3. var table = db get table

4. var updated =  item
   - Expected: table.update_row("item-2", updated) is true
   - Expected: table.mark_deleted("item-1") is true

5. db set table
   - Expected: db.save() is true
   - Expected: loaded_table.get_row("item-2").unwrap().get("name").unwrap() equals `beta-updated`
   - Expected: loaded_table.get_row("item-1").unwrap().get("valid").unwrap() equals `false`
   - Expected: loaded_table.valid_rows().len() equals `1`

6.  cleanup


<details>
<summary>Executable SPipe</summary>

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

1.  cleanup

2. var db =  database with items
   - Expected: db.save() is true
   - Expected: query_opt.? is true

3.  filter by

4.  order by

5.  execute
   - Expected: rows.len() equals `1`
   - Expected: rows[0].get("id").unwrap() equals `item-1`

6.  cleanup


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("query")
_cleanup(path)

var db = _database_with_items(path)
expect(db.save()).to_equal(true)
val loaded = load_sdn_database(path)?
val query_opt = query_table(loaded, "items")
expect(query_opt.?).to_equal(true)
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

1.  cleanup

2. var db = SdnDatabase new
   - Expected: db.import_table_sdn("not a table") is false
   - Expected: db.get_table("not").? is false
   - Expected: db.modified is false

3.  cleanup


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _db_path("malformed")
_cleanup(path)

var db = SdnDatabase.new(path)
expect(db.import_table_sdn("not a table")).to_equal(false)
expect(db.get_table("not").?).to_equal(false)
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Database system production workflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
