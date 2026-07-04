# Mini Db Specification

> 1. var db = TestDatabase empty

<!-- sdn-diagram:id=_mini_db_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_mini_db_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_mini_db_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_mini_db_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mini Db Specification

## Scenarios

### debug

#### first - uses db

1. var db = TestDatabase empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var db = TestDatabase.empty()
# update_test_result has 6 params in source but compiled SMF may differ
# Just verify db creation and initial state
expect(db.tests.len()).to_be(0)
```

</details>

#### second - validate

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = RunRecord(
    run_id: "",
    start_time: "invalid",
    end_time: "invalid",
    pid: -1,
    hostname: "",
    status: "BadStatus",
    test_count: 0,
    passed: 10,
    failed: 10,
    crashed: 0,
    timed_out: 0
)
val report = validate_run_record(r)
expect(report.has_violations()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/_mini_db_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
