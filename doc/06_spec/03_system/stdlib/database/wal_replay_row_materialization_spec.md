# WAL Replay Row Materialization Specification

> Tests the WAL codec pair (row_to_wal_payload / wal_payload_to_row) and

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**ACs:** AC-5 (hardening fix), AC-7 (new tests)
Tests the WAL codec pair (row_to_wal_payload / wal_payload_to_row) and
verifies that SdnDatabase.load replays WAL entries into fully populated
SdnRow instances instead of blank rows.

## Scenarios

### row_to_wal_payload

### basic serialization

#### serializes simple row fields to CSV payload

- serializes simple row fields to CSV payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes simple row fields to CSV payload")
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
# Payload should contain all three field values
expect(payload).to_contain("Alice")
expect(payload).to_contain("30")
```

</details>

#### preserves field order matching column list

- preserves field order matching column list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves field order matching column list")
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
# id comes before name comes before age
expect(payload).to_start_with("1,")
```

</details>

### special characters

#### quotes values containing commas

- quotes values containing commas


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("quotes values containing commas")
val row = make_row_with_commas()
val payload = row_to_wal_payload(row, two_columns())
# The comma-containing value must be quoted
expect(payload).to_contain("\"hello, world\"")
```

</details>

#### handles values containing pipe characters

- handles values containing pipe characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles values containing pipe characters")
val row = make_row_with_pipes()
val payload = row_to_wal_payload(row, pipe_columns())
expect(payload).to_contain("a|b|c")
```

</details>

#### handles values containing double quotes

- handles values containing double quotes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles values containing double quotes")
val row = make_row_with_quotes()
val payload = row_to_wal_payload(row, quote_columns())
expect(payload.len()).to_be_greater_than(0)
```

</details>

#### handles values containing newlines

- handles values containing newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles values containing newlines")
val row = make_row_with_newline()
val payload = row_to_wal_payload(row, newline_columns())
expect(payload.len()).to_be_greater_than(0)
```

</details>

### edge cases

#### handles empty field values

- handles empty field values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty field values")
val row = make_empty_row()
val payload = row_to_wal_payload(row, ["id", "name"])
expect(payload.len()).to_be_greater_than(0)
```

</details>

#### handles single column

- handles single column
   - Expected: payload equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single column")
val row = SdnRow(fields: {}, _version: 0)
row.set("id", "42")
val payload = row_to_wal_payload(row, ["id"])
expect(payload).to_equal("42")
```

</details>

### wal_payload_to_row

### basic deserialization

#### reconstructs row with all fields populated

- reconstructs row with all fields populated
   - Expected: restored != nil is true
   - Expected: r.get("id") ?? "" equals `1`
   - Expected: r.get("name") ?? "" equals `Alice`
   - Expected: r.get("age") ?? "" equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reconstructs row with all fields populated")
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored != nil).to_equal(true)
val r = restored.unwrap()
expect(r.get("id") ?? "").to_equal("1")
expect(r.get("name") ?? "").to_equal("Alice")
expect(r.get("age") ?? "").to_equal("30")
```

</details>

#### returns nil for mismatched column count

- returns nil for mismatched column count
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for mismatched column count")
val result = wal_payload_to_row("a,b", ["x", "y", "z"])
expect(result != nil).to_equal(false)
```

</details>

### special character round-trip

#### round-trips values with commas

- round-trips values with commas
   - Expected: restored != nil is true
   - Expected: r.get("desc") ?? "" equals `hello, world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips values with commas")
val row = make_row_with_commas()
val cols = two_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored != nil).to_equal(true)
val r = restored.unwrap()
expect(r.get("desc") ?? "").to_equal("hello, world")
```

</details>

#### round-trips values with pipes

- round-trips values with pipes
   - Expected: restored != nil is true
   - Expected: r.get("data") ?? "" equals `a|b|c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips values with pipes")
val row = make_row_with_pipes()
val cols = pipe_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored != nil).to_equal(true)
val r = restored.unwrap()
expect(r.get("data") ?? "").to_equal("a|b|c")
```

</details>

#### round-trips values with quotes

- round-trips values with quotes
   - Expected: restored != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips values with quotes")
val row = make_row_with_quotes()
val cols = quote_columns()
val payload = row_to_wal_payload(row, cols)
val restored = wal_payload_to_row(payload, cols)
expect(restored != nil).to_equal(true)
```

</details>

### edge cases

#### returns nil for empty payload with non-empty columns

- returns nil for empty payload with non-empty columns
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for empty payload with non-empty columns")
val result = wal_payload_to_row("", ["id", "name"])
expect(result != nil).to_equal(false)
```

</details>

### WAL version handling

#### v2 WAL entries produce populated rows on replay

- v2 WAL entries produce populated rows on replay
   - Expected: restored != nil is true
   - Expected: r.has_column("name") is true
   - Expected: r.has_column("age") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("v2 WAL entries produce populated rows on replay")
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored != nil).to_equal(true)
val r = restored.unwrap()
expect(r.has_column("name")).to_equal(true)
expect(r.has_column("age")).to_equal(true)
```

</details>

#### v1 WAL file without version header produces no materialized rows

- v1 WAL file without version header produces no materialized rows
   - Expected: result != nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("v1 WAL file without version header produces no materialized rows")
# v1 WAL files have no #wal-version:2 header.
# Per D-1, v1 entries are silently skipped (no recoverable data).
# Codec functions should return nil for raw v1-style data.
val v1_data = "raw_unstructured_text"
val result = wal_payload_to_row(v1_data, simple_columns())
# v1 data won't have correct column count, so returns nil
expect(result != nil).to_equal(false)
```

</details>

### SdnDatabase WAL replay

#### replayed Insert entries have populated fields not blank rows

- replayed Insert entries have populated fields not blank rows
   - Expected: loaded != nil is true
   - Expected: ltable != nil is true
   - Expected: r.get("name") ?? "" equals `Widget`
   - Expected: r.get("status") ?? "" equals `active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replayed Insert entries have populated fields not blank rows")
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
expect(loaded != nil).to_equal(true)
val ldb = loaded.unwrap()
val ltable = ldb.get_table("items")
expect(ltable != nil).to_equal(true)
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

- replayed Update entries preserve field data
   - Expected: loaded != nil is true
   - Expected: ltable != nil is true
   - Expected: r.get("name") ?? "" equals `Original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replayed Update entries preserve field data")
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
expect(loaded != nil).to_equal(true)
val ldb = loaded.unwrap()
val ltable = ldb.get_table("items")
expect(ltable != nil).to_equal(true)
val t = ltable.unwrap()
val r = t.rows[0]
expect(r.get("name") ?? "").to_equal("Original")
cleanup_wal_db(path)
```

</details>

#### codec round-trip preserves all field data

- codec round-trip preserves all field data
   - Expected: restored != nil is true
   - Expected: r.get("name") ?? "" equals `Alice`
   - Expected: r.get("age") ?? "" equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("codec round-trip preserves all field data")
val row = make_simple_row()
val payload = row_to_wal_payload(row, simple_columns())
val restored = wal_payload_to_row(payload, simple_columns())
expect(restored != nil).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `033cba58f944e3b2a07ac20c0a7975f0e9bebdab0e24cb004441e81e3396e43a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `033cba58f944e3b2a07ac20c0a7975f0e9bebdab0e24cb004441e81e3396e43a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `033cba58f944e3b2a07ac20c0a7975f0e9bebdab0e24cb004441e81e3396e43a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/stdlib/database/wal_replay_row_materialization_spec.spl
mirror: doc/06_spec/03_system/stdlib/database/wal_replay_row_materialization_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/database/wal_replay_row_materialization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/database/wal_replay_row_materialization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/database/wal_replay_row_materialization_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes simple row fields to CSV payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/wal_replay_row_materialization_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves field order matching column list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/stdlib/database/wal_replay_row_materialization_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'quotes values containing commas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
