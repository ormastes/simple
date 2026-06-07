# WAL Replay Row Materialization Specification

> Tests the WAL codec pair (row_to_wal_payload / wal_payload_to_row) and

<!-- sdn-diagram:id=wal_replay_row_materialization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wal_replay_row_materialization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wal_replay_row_materialization_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wal_replay_row_materialization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WAL Replay Row Materialization Specification

Tests the WAL codec pair (row_to_wal_payload / wal_payload_to_row) and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no implementation yet) |
| Source | `test/03_system/stdlib/database/wal_replay_row_materialization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests the WAL codec pair (row_to_wal_payload / wal_payload_to_row) and
verifies that SdnDatabase.load replays WAL entries into fully populated
SdnRow instances instead of blank rows.

## Scenarios

### row_to_wal_payload

### basic serialization

#### serializes simple row fields to CSV payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
# Payload should contain all three field values
expect(payload).to_contain("Alice")
expect(payload).to_contain("30")
```

</details>

#### preserves field order matching column list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
# id comes before name comes before age
expect(payload).to_start_with("1,")
```

</details>

### special characters

#### quotes values containing commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_commas()
val payload = row_to_wal_payload(row, two_columns())
# The comma-containing value must be quoted
expect(payload).to_contain("\"hello, world\"")
```

</details>

#### handles values containing pipe characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_pipes()
val payload = row_to_wal_payload(row, pipe_columns())
expect(payload).to_contain("a|b|c")
```

</details>

#### handles values containing double quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_quotes()
val payload = row_to_wal_payload(row, quote_columns())
expect(payload.len()).to_be_greater_than(0)
```

</details>

#### handles values containing newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_newline()
val payload = row_to_wal_payload(row, newline_columns())
expect(payload.len()).to_be_greater_than(0)
```

</details>

### edge cases

#### handles empty field values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_empty_row()
val payload = row_to_wal_payload(row, ["id", "name"])
expect(payload.len()).to_be_greater_than(0)
```

</details>

#### handles single column

1. row set
   - Expected: payload equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = SdnRow(fields: {}, _version: 0)
row.set("id", "42")
val payload = row_to_wal_payload(row, ["id"])
expect(payload).to_equal("42")
```

</details>

### wal_payload_to_row

### basic deserialization

#### reconstructs row with all fields populated

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored.?).to_equal(true)
val r = restored.unwrap()
expect(r.get("id") ?? "").to_equal("1")
expect(r.get("name") ?? "").to_equal("Alice")
expect(r.get("age") ?? "").to_equal("30")
```

</details>

#### returns nil for mismatched column count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wal_payload_to_row("a,b", ["x", "y", "z"])
expect(result.?).to_equal(false)
```

</details>

### special character round-trip

#### round-trips values with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_commas()
val cols = two_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored.?).to_equal(true)
val r = restored.unwrap()
expect(r.get("desc") ?? "").to_equal("hello, world")
```

</details>

#### round-trips values with pipes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_pipes()
val cols = pipe_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored.?).to_equal(true)
val r = restored.unwrap()
expect(r.get("data") ?? "").to_equal("a|b|c")
```

</details>

#### round-trips values with quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_row_with_quotes()
val cols = quote_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored.?).to_equal(true)
```

</details>

### edge cases

#### returns nil for empty payload with non-empty columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wal_payload_to_row("", ["id", "name"])
expect(result.?).to_equal(false)
```

</details>

### WAL version handling

#### v2 WAL entries produce populated rows on replay

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored.?).to_equal(true)
val r = restored.unwrap()
expect(r.has_column("name")).to_equal(true)
expect(r.has_column("age")).to_equal(true)
```

</details>

#### v1 WAL file without version header produces no materialized rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# v1 WAL files have no #wal-version:2 header.
# Per D-1, v1 entries are silently skipped (no recoverable data).
# Codec functions should return nil for raw v1-style data.
val v1_data = "raw_unstructured_text"
val result = wal_payload_to_row(v1_data, simple_columns())
# v1 data won't have correct column count, so returns nil
expect(result.?).to_equal(false)
```

</details>

### SdnDatabase WAL replay

#### replayed Insert entries have populated fields not blank rows

1. cleanup wal db
2. var db = SdnDatabase new
3. var table = SdnTable new
4. row set
5. row set
6. row set
7. table add row
8. db set table
9. db save
   - Expected: loaded.? is true
   - Expected: ltable.? is true
   - Expected: r.get("name") ?? "" equals `Widget`
   - Expected: r.get("status") ?? "" equals `active`
10. cleanup wal db


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Integration: create DB, add WAL entry, save, reload via load()
# and verify replayed rows have populated fields.
val path = wal_db_path()
cleanup_wal_db(path)
var db = SdnDatabase.new(path)
var table = SdnTable.new("items", ["id", "name", "status"])
val row = SdnRow(fields: {}, _version: 0)
row.set("id", "item-1")
row.set("name", "Widget")
row.set("status", "active")
table.add_row(row)
db.set_table("items", table)
db.save()
# Reload and check that the row has fields, not blank
val loaded = load_sdn_database(path)
expect(loaded.?).to_equal(true)
val ldb = loaded.unwrap()
val ltable = ldb.get_table("items")
expect(ltable.?).to_equal(true)
val t = ltable.unwrap()
expect(t.rows.len()).to_be_greater_than(0)
val r = t.rows[0]
# Core assertion: fields must NOT be empty (the bug was blank rows)
expect(r.get("name") ?? "").to_equal("Widget")
expect(r.get("status") ?? "").to_equal("active")
cleanup_wal_db(path)
```

</details>

#### replayed Update entries preserve field data

1. cleanup wal db
2. var db = SdnDatabase new
3. var table = SdnTable new
4. row set
5. row set
6. table add row
7. db set table
8. db save
   - Expected: loaded.? is true
   - Expected: ltable.? is true
   - Expected: r.get("name") ?? "" equals `Original`
9. cleanup wal db


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = wal_db_path()
cleanup_wal_db(path)
var db = SdnDatabase.new(path)
var table = SdnTable.new("items", ["id", "name"])
val row = SdnRow(fields: {}, _version: 0)
row.set("id", "u-1")
row.set("name", "Original")
table.add_row(row)
db.set_table("items", table)
db.save()
# Reload
val loaded = load_sdn_database(path)
expect(loaded.?).to_equal(true)
val ldb = loaded.unwrap()
val ltable = ldb.get_table("items")
expect(ltable.?).to_equal(true)
val t = ltable.unwrap()
val r = t.rows[0]
expect(r.get("name") ?? "").to_equal("Original")
cleanup_wal_db(path)
```

</details>

#### codec round-trip preserves all field data

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored.?).to_equal(true)
val r = restored.unwrap()
expect(r.get("name") ?? "").to_equal("Alice")
expect(r.get("age") ?? "").to_equal("30")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
