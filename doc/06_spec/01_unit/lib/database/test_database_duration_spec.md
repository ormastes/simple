# Test Database Duration Specification

> Tests covering TestDatabase duration parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Database Duration Specification

## Scenarios

### TestDatabase duration parsing

#### starts and completes a run through portable host facades

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts and completes a run through portable host facades
   - Expected: db.end_run(run_id, RunStatus.Completed) is true
   - Expected: db.get_run(run_id).unwrap().end_time != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts and completes a run through portable host facades")
val db = create_test_database("unused-runtime-facade.sdn")
val run_id = db.start_run()

expect(run_id).to_start_with("run_")
expect(run_id.len()).to_be_greater_than(4)
expect(db.end_run(run_id, RunStatus.Completed)).to_equal(true)
expect(db.get_run(run_id).unwrap().end_time != nil).to_equal(true)
```

</details>

#### treats malformed stored durations as zero

- treats malformed stored durations as zero
   - Expected: db.stats().avg_duration_ms equals `0.0`
   - Expected: db.slow_tests(0.0).len() equals `0`
   - Expected: db.get_result("bad_duration", "run_1").unwrap().duration_ms equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("treats malformed stored durations as zero")
val db = create_test_database("unused.sdn")
val row = SdnRow.empty()
row.set("test_name", "bad_duration")
row.set("run_id", "run_1")
row.set("status", "passed")
row.set("duration_ms", "nope")
row.set("error_message", "")
row.set("timestamp", "now")
row.set("valid", "true")
db.db.add_row_to_table("test_results", row)

expect(db.stats().avg_duration_ms).to_equal(0.0)
expect(db.slow_tests(0.0).len()).to_equal(0)
expect(db.get_result("bad_duration", "run_1").unwrap().duration_ms).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/test_database_duration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestDatabase duration parsing.
- TestDatabase duration parsing

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `233987845f665ea76d927ebd051642e2ad3d7ec3f7fc1ec8eab2e2c2abf7d0dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `233987845f665ea76d927ebd051642e2ad3d7ec3f7fc1ec8eab2e2c2abf7d0dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `233987845f665ea76d927ebd051642e2ad3d7ec3f7fc1ec8eab2e2c2abf7d0dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/database/test_database_duration_spec.spl
mirror: doc/06_spec/01_unit/lib/database/test_database_duration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/test_database_duration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/test_database_duration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/test_database_duration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/database/test_database_duration_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts and completes a run through portable host facades' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/test_database_duration_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats malformed stored durations as zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
