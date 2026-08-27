# Hooks Detectors Facade Specification

> Tests covering nogc_async_mut hooks detectors facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hooks Detectors Facade Specification

## Scenarios

### nogc_async_mut hooks detectors facade

#### re-exports detector summaries and priority helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports detector summaries and priority helpers
   - Expected: build.total_errors equals `0`
   - Expected: format_build_summary(build) equals `No build issues found`
   - Expected: features.total equals `0`
   - Expected: format_feature_summary(features) equals `No features found`
   - Expected: tasks.total equals `0`
   - Expected: format_task_summary(tasks) equals `No tasks found`
   - Expected: todos.total equals `0`
   - Expected: format_todo_summary(todos) equals `No TODOs found`
   - Expected: get_priority_value("P1") equals `1`
   - Expected: get_priority_value("PX") equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports detector summaries and priority helpers")
val missing = "__missing_hooks_detector_db__.sdn"
val build = detect_build_issues(missing)
expect(build.total_errors).to_equal(0)
expect(format_build_summary(build)).to_equal("No build issues found")
val features = detect_features(missing)
expect(features.total).to_equal(0)
expect(format_feature_summary(features)).to_equal("No features found")
val tasks = detect_tasks(missing)
expect(tasks.total).to_equal(0)
expect(format_task_summary(tasks)).to_equal("No tasks found")
val todos = detect_todos(missing, 1)
expect(todos.total).to_equal(0)
expect(format_todo_summary(todos)).to_equal("No TODOs found")
expect(get_priority_value("P1")).to_equal(1)
expect(get_priority_value("PX")).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut hooks detectors facade.
- nogc_async_mut hooks detectors facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e05614f9109bdf62c9bddf0b17d43b9a49991c14bc773801fad98fba9146db0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e05614f9109bdf62c9bddf0b17d43b9a49991c14bc773801fad98fba9146db0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e05614f9109bdf62c9bddf0b17d43b9a49991c14bc773801fad98fba9146db0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports detector summaries and priority helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
