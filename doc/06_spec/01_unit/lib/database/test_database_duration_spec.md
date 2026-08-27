# Test Database Duration Specification

> <details>

<!-- sdn-diagram:id=test_database_duration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_database_duration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_database_duration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_database_duration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Database Duration Specification

## Scenarios

### TestDatabase duration parsing

#### treats malformed stored durations as zero

- row set
- row set
- row set
- row set
- row set
- row set
- row set
- db db add row to table
   - Expected: db.stats().avg_duration_ms equals `0.0`
   - Expected: db.slow_tests(0.0).len() equals `0`
   - Expected: db.get_result("bad_duration", "run_1").unwrap().duration_ms equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestDatabase duration parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
