# Pure-Simple SQL: parameter-free SELECT results stay current after INSERT

> Embedded tier (`std.database.pure_sql`, see

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure-Simple SQL: parameter-free SELECT results stay current after INSERT

Embedded tier (`std.database.pure_sql`, see

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/pure_sql_select_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Embedded tier (`std.database.pure_sql`, see
doc/07_guide/lib/database/db_implementations_map.md). A parameter-free
SELECT is cached per table keyed by its SQL text; a plain INSERT must
invalidate that slot so a byte-identical literal `WHERE` re-run sees the
new row, exactly like the `?`-bound form (which never consults the cache).
Reproduces doc/08_tracking/bug/llm_caret_pure_sql_where_text_pk_returns_no_rows_2026-08-25.md.

## Scenarios

### pure_sql literal WHERE after INSERT

#### re-runs a byte-identical text-pk literal SELECT after a plain INSERT
#### answers identically before and after checkpoint on a deferred file store

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/pure_sql_select_cache_spec.db"
val db = PureDatabase.open_deferred(path).unwrap()
expect(db.exec_sql("CREATE TABLE IF NOT EXISTS mm (id TEXT PRIMARY KEY, value TEXT, n INTEGER)").is_ok()).to_equal(true)
expect(db.exec_sql("DELETE FROM mm").is_ok()).to_equal(true)
val sql = "SELECT value FROM mm WHERE id = 'schema_version'"
expect(count(db, sql)).to_equal(0)
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('schema_version','1',1)").is_ok()).to_equal(true)
expect(db.checkpoint().is_ok()).to_equal(true)
db.set_auto_checkpoint(true)
expect(count(db, sql)).to_equal(1)
expect(count_bound(db, "SELECT value FROM mm WHERE id = ?", DbValue.Text(value: "schema_version"))).to_equal(1)
```

</details>

#### single-quoted literal with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = fresh()
val sql = "SELECT n FROM mm WHERE id = 'two words here'"
expect(count(db, sql)).to_equal(0)
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('two words here','x',2)").is_ok()).to_equal(true)
expect(count(db, sql)).to_equal(1)
```

</details>

#### literal with an escaped quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = fresh()
val sql = "SELECT n FROM mm WHERE id = 'it''s'"
expect(count(db, sql)).to_equal(0)
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('it''s','x',3)").is_ok()).to_equal(true)
expect(count(db, sql)).to_equal(1)
expect(count_bound(db, "SELECT n FROM mm WHERE id = ?", DbValue.Text(value: "it's"))).to_equal(1)
```

</details>

#### WHERE on a non-pk text column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = fresh()
val sql = "SELECT id FROM mm WHERE value = 'needle'"
expect(count(db, sql)).to_equal(0)
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('k1','needle',4)").is_ok()).to_equal(true)
expect(count(db, sql)).to_equal(1)
```

</details>

#### WHERE on an integer literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = fresh()
val sql = "SELECT id FROM mm WHERE n = 42"
expect(count(db, sql)).to_equal(0)
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('k2','x',42)").is_ok()).to_equal(true)
expect(count(db, sql)).to_equal(1)
```

</details>

#### bound and literal forms agree after every insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = fresh()
val lit = "SELECT value FROM mm WHERE id = 'a'"
val bound = "SELECT value FROM mm WHERE id = ?"
expect(count(db, lit)).to_equal(count_bound(db, bound, DbValue.Text(value: "a")))
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('a','1',1)").is_ok()).to_equal(true)
expect(count(db, lit)).to_equal(count_bound(db, bound, DbValue.Text(value: "a")))
expect(db.exec_sql("INSERT INTO mm (id,value,n) VALUES ('b','2',2)").is_ok()).to_equal(true)
expect(count(db, "SELECT id FROM mm")).to_equal(2)
expect(count(db, lit)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-DATABASE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8cd037cee41f883b5a092e70fff337cf0c84fd8d3304bc0e5eb5e177b20a4c71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cd037cee41f883b5a092e70fff337cf0c84fd8d3304bc0e5eb5e177b20a4c71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cd037cee41f883b5a092e70fff337cf0c84fd8d3304bc0e5eb5e177b20a4c71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/database/pure_sql_select_cache_spec.spl
mirror: doc/06_spec/01_unit/lib/database/pure_sql_select_cache_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/lib/database/pure_sql_select_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/pure_sql_select_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 're-runs a byte-identical text-pk literal SELECT after a plain INSERT' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'answers identically before and after checkpoint on a deferred file store' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'single-quoted literal with spaces' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/database/pure_sql_select_cache_spec.spl:73:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'literal with an escaped quote' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
