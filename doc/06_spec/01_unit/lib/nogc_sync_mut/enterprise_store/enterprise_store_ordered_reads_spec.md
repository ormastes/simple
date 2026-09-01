# Enterprise Store — deterministic ordered reads

> `store_rows` used to issue `SELECT <cols> FROM <table>` with NO ORDER BY. Several enterprise consumers treat the LAST row encountered as current state or effective rate (e.g. `hcm_wage_at` tie-break on equal `effective_epoch`), but SQL row order without ORDER BY is unspecified on a real engine. The store read path now appends `ORDER BY id`, making "last row" well-defined as the highest-id (latest-inserted) row.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enterprise Store — deterministic ordered reads

`store_rows` used to issue `SELECT <cols> FROM <table>` with NO ORDER BY. Several enterprise consumers treat the LAST row encountered as current state or effective rate (e.g. `hcm_wage_at` tie-break on equal `effective_epoch`), but SQL row order without ORDER BY is unspecified on a real engine. The store read path now appends `ORDER BY id`, making "last row" well-defined as the highest-id (latest-inserted) row.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/01_research/app/office/office_enterprise_suite_audit_architecture_parallel_plan_2026-08-20.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`store_rows` used to issue `SELECT <cols> FROM <table>` with NO ORDER BY.
Several enterprise consumers treat the LAST row encountered as current
state or effective rate (e.g. `hcm_wage_at` tie-break on equal
`effective_epoch`), but SQL row order without ORDER BY is unspecified on a
real engine. The store read path now appends `ORDER BY id`, making "last
row" well-defined as the highest-id (latest-inserted) row.

Note on backends: the interpreter's rt_sqlite emulation returns rows in
insertion order and ignores ORDER BY, so it cannot reproduce the disorder;
this spec pins the ordered CONTRACT (ids strictly ascending; tie-break
picks the highest-id row) which the ORDER BY guarantees on real SQLite.

**Requirements:** N/A
**Plan:** doc/01_research/app/office/office_enterprise_suite_audit_architecture_parallel_plan_2026-08-20.md

## Scenarios

### enterprise store — store_rows returns rows in ascending id order

#### reads back inserted rows ordered by id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads back inserted rows ordered by id
- Open a store and create a table
- Insert five rows
- Verify ids come back strictly ascending — the ordered-read contract
   - Expected: rows.len() equals `5`
- The LAST row is the latest-inserted one
   - Expected: sqlite_row_get(rows[rows.len() - 1], "payload") equals `p5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads back inserted rows ordered by id")
step("Open a store and create a table")
val store = store_open(":memory:")
expect(store.open_ok).to_be(true)
store_migrate(store, "ord_001_events",
    "CREATE TABLE IF NOT EXISTS ord_events (id INTEGER PRIMARY KEY, tenant_id TEXT, payload TEXT)")
step("Insert five rows")
var i = 1
while i <= 5:
    store_insert_row(store,
        "INSERT INTO ord_events (tenant_id, payload) VALUES (?, ?)",
        ["t1", "p" + i.to_text()])
    i = i + 1
step("Verify ids come back strictly ascending — the ordered-read contract")
val rows = store_rows(store, "ord_events", "id, tenant_id, payload")
expect(rows.len()).to_equal(5)
var prev: i64 = 0
for row in rows:
    val id = int(sqlite_row_get(row, "id"))
    expect(id > prev).to_be(true)
    prev = id
step("The LAST row is the latest-inserted one")
expect(sqlite_row_get(rows[rows.len() - 1], "payload")).to_equal("p5")
store_close(store)
```

</details>

### enterprise hcm — effective wage tie-break is the latest amendment

#### picks the highest-id contract row when effective_epoch ties

- picks the highest-id contract row when effective_epoch ties
- Open a store with the HCM schema
- Insert two contracts with the SAME effective_epoch (amendment)
- The effective wage is the later amendment (highest id), deterministically
   - Expected: hcm_wage_at(store, "t1", "emp-1", 2000) equals `1800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("picks the highest-id contract row when effective_epoch ties")
step("Open a store with the HCM schema")
val store = store_open(":memory:")
expect(hcm_setup(store)).to_be(true)
step("Insert two contracts with the SAME effective_epoch (amendment)")
store_insert_row(store,
    "INSERT INTO hcm_contracts (tenant_id, employee_id, effective_epoch, wage_cents_per_hour, weekly_hours) VALUES (?, ?, ?, ?, ?)",
    ["t1", "emp-1", "1000", "1500", "40"])
store_insert_row(store,
    "INSERT INTO hcm_contracts (tenant_id, employee_id, effective_epoch, wage_cents_per_hour, weekly_hours) VALUES (?, ?, ?, ?, ?)",
    ["t1", "emp-1", "1000", "1800", "40"])
step("The effective wage is the later amendment (highest id), deterministically")
expect(hcm_wage_at(store, "t1", "emp-1", 2000)).to_equal(1800)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/01_research/app/office/office_enterprise_suite_audit_architecture_parallel_plan_2026-08-20.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a609ea886055c955ae1f35a394a72b7c9e4f637725e93adf71be730af96adc89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a609ea886055c955ae1f35a394a72b7c9e4f637725e93adf71be730af96adc89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a609ea886055c955ae1f35a394a72b7c9e4f637725e93adf71be730af96adc89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads back inserted rows ordered by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_ordered_reads_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'picks the highest-id contract row when effective_epoch ties' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
