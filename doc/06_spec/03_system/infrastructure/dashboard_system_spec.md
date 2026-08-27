# Dashboard System Specification

> Tests covering Dashboard System Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard System Specification

## Scenarios

### Dashboard System Tests

#### collect generates dashboard tables and cache

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collect generates dashboard tables and cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collect generates dashboard tables and cache")
val result = run_simple(["collect", "--mode=full"])
verify(result.exit_code == 0)
verify(result.stdout.contains("Collection complete."))

verify(file_exists("doc/10_metrics/dashboard/tables/todos.sdn"))
verify(file_exists("doc/10_metrics/dashboard/tables/test_status.sdn"))
verify(file_exists("doc/10_metrics/dashboard/dashboard_db.cache.sdn"))

val todos = file_read("doc/10_metrics/dashboard/tables/todos.sdn")
verify(todos.contains("todos |"))
```

</details>

#### status prints summary

- status prints summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("status prints summary")

val result = run_simple(["status"])
verify(result.exit_code == 0)
verify(result.stdout.contains("Project Status Overview"))
verify(result.stdout.contains("Todos:"))
```

</details>

#### spipe summary prints suite/test counts

- spipe summary prints suite/test counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spipe summary prints suite/test counts")

val result = run_simple(["spipe"])
verify(result.exit_code == 0)
verify(result.stdout.contains("SPipe Test Summary"))
verify(result.stdout.contains("Suites:"))
verify(result.stdout.contains("Tests:"))
```

</details>

#### export json includes summary and tables

- export json includes summary and tables


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("export json includes summary and tables")

val result = run_simple(["export", "--format=json"])
verify(result.exit_code == 0)
verify(result.stdout.contains("\"summary\""))
verify(result.stdout.contains("\"tables\""))
verify(result.stdout.contains("\"todos\""))
```

</details>

#### snapshot creates history file for today

- snapshot creates history file for today


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("snapshot creates history file for today")

val date = shell_output("date +%Y-%m-%d")
val month = shell_output("date +%Y-%m")
verify(date.len() > 0)
verify(month.len() > 0)

val snapshot_path = "doc/10_metrics/dashboard/history/{month}/{date}.sdn"
# Remove existing snapshot to ensure creation is exercised
if file_exists(snapshot_path):
    file_delete(snapshot_path)

val result = run_simple(["snapshot"])
verify(result.exit_code == 0)
verify(file_exists(snapshot_path))

val snapshot = file_read(snapshot_path)
verify(snapshot.contains("todos |"))
verify(snapshot.contains("features |"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/dashboard_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Dashboard System Tests.
- Dashboard System Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `6d465b092d6517d495db5bb149f5197b09a4dc1763bed6d75fcd4f525eb1c66b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d465b092d6517d495db5bb149f5197b09a4dc1763bed6d75fcd4f525eb1c66b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d465b092d6517d495db5bb149f5197b09a4dc1763bed6d75fcd4f525eb1c66b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/infrastructure/dashboard_system_spec.spl
mirror: doc/06_spec/03_system/infrastructure/dashboard_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infrastructure/dashboard_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/dashboard_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/dashboard_system_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collect generates dashboard tables and cache' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/dashboard_system_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'status prints summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/dashboard_system_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spipe summary prints suite/test counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
