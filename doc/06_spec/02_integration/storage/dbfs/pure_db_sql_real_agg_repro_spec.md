# Pure Db Sql Real Agg Repro Specification

> Tests covering PureDatabase SUM/AVG on REAL column.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Db Sql Real Agg Repro Specification

## Scenarios

### PureDatabase SUM/AVG on REAL column

#### supports SUM aggregate on a REAL column

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- supports SUM aggregate on a REAL column
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `31.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports SUM aggregate on a REAL column")
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE smr (id INTEGER, val REAL)").unwrap()
db.exec_sql("INSERT INTO smr (id, val) VALUES (1, 10.5)").unwrap()
db.exec_sql("INSERT INTO smr (id, val) VALUES (2, 20.5)").unwrap()
val rows = db.query("SELECT SUM(val) FROM smr", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("31.0")
```

</details>

#### supports AVG aggregate on a REAL column

- supports AVG aggregate on a REAL column
   - Expected: rows.len() equals `1`
   - Expected: rows[0].values[0].to_text() equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports AVG aggregate on a REAL column")
val r = PureDatabase.memory()
var db = r.unwrap()
db.exec_sql("CREATE TABLE avr (id INTEGER, val REAL)").unwrap()
db.exec_sql("INSERT INTO avr (id, val) VALUES (1, 10.0)").unwrap()
db.exec_sql("INSERT INTO avr (id, val) VALUES (2, 20.0)").unwrap()
val rows = db.query("SELECT AVG(val) FROM avr", []).unwrap()
expect(rows.len()).to_equal(1)
expect(rows[0].values[0].to_text()).to_equal("15.0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PureDatabase SUM/AVG on REAL column.
- PureDatabase SUM/AVG on REAL column

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `0885e69f8401b77c99d181ed87847afe4deec7c18e8042222a8bb476700644d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0885e69f8401b77c99d181ed87847afe4deec7c18e8042222a8bb476700644d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0885e69f8401b77c99d181ed87847afe4deec7c18e8042222a8bb476700644d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports SUM aggregate on a REAL column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/pure_db_sql_real_agg_repro_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports AVG aggregate on a REAL column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
