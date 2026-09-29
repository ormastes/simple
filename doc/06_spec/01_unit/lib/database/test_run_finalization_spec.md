# Test Run Finalization Specification

> Tests covering Test run finalization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Run Finalization Specification

## Scenarios

### Test run finalization

#### updates a row keyed by the table's own primary key column

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- updates a row keyed by the table's own primary key column
   - Expected: table.rows[0].get("status") ?? "" equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("updates a row keyed by the table's own primary key column")
val table = SdnTable(
    name: "test_runs",
    columns: ["run_id", "status"],
    rows: [],
    index: {}
)
val row = SdnRow.empty()
row.set("run_id", "run_1")
row.set("status", "running")
table.add_row(row)

val updated = SdnRow.empty()
updated.set("run_id", "run_1")
updated.set("status", "completed")
# Pre-fix: false — update_row looked for a column named "id".
assert_true(table.update_row("run_1", updated))
expect(table.rows[0].get("status") ?? "").to_equal("completed")
```

</details>

#### transitions a started run to completed

- transitions a started run to completed
   - Expected: running.len() equals `1`
   - Expected: db.list_runs("running").len() equals `0`
   - Expected: completed.len() equals `1`
   - Expected: completed[0].passed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("transitions a started run to completed")
var db = create_test_database_extended("build/test/test_run_finalization.sdn")
val run_id = db.start_run()

val running = db.list_runs("running")
expect(running.len()).to_equal(1)

db.complete_run(run_id: run_id, test_count: 1, passed: 1, failed: 0, timed_out: 0)

# Pre-fix: still 1 running, 0 completed — the run never finalized.
expect(db.list_runs("running").len()).to_equal(0)
val completed = db.list_runs("completed")
expect(completed.len()).to_equal(1)
expect(completed[0].passed).to_equal(1)
```

</details>

#### records a verdict on the test row instead of leaving it unknown

- records a verdict on the test row instead of leaving it unknown
   - Expected: db.tests_by_status("passed").len() equals `1`
   - Expected: db.tests_by_status("unknown").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records a verdict on the test row instead of leaving it unknown")
var db = create_test_database_extended("build/test/test_run_verdict.sdn")
val run_id = db.start_run()
db.update_test_result(
    file_path: "test/example_spec.spl",
    suite_name: "spec",
    test_name: "test/example_spec.spl",
    status: "passed",
    duration_ms: 1.0,
    run_id: run_id
)
db.complete_run(run_id: run_id, test_count: 1, passed: 1, failed: 0, timed_out: 0)

# Pre-fix: (1, 0, 0, 0) — one known test, zero verdicts.
expect(db.tests_by_status("passed").len()).to_equal(1)
expect(db.tests_by_status("unknown").len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/test_run_finalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Test run finalization.
- Test run finalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5275959f86878e3d83efde8bf883e684dbcc05721641729cadd758847afe97fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5275959f86878e3d83efde8bf883e684dbcc05721641729cadd758847afe97fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5275959f86878e3d83efde8bf883e684dbcc05721641729cadd758847afe97fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/database/test_run_finalization_spec.spl
mirror: doc/06_spec/01_unit/lib/database/test_run_finalization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/test_run_finalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/test_run_finalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/test_run_finalization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/database/test_run_finalization_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates a row keyed by the table's own primary key column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/test_run_finalization_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transitions a started run to completed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/test_run_finalization_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a verdict on the test row instead of leaving it unknown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
