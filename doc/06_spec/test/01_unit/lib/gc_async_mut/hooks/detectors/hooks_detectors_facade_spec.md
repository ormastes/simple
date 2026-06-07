# Hooks Detectors Facade Specification

> <details>

<!-- sdn-diagram:id=hooks_detectors_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hooks_detectors_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hooks_detectors_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hooks_detectors_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hooks Detectors Facade Specification

## Scenarios

### gc_async_mut hooks detectors facade

#### re-exports detector summaries and priority helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/gc_async_mut/hooks/detectors/hooks_detectors_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut hooks detectors facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
