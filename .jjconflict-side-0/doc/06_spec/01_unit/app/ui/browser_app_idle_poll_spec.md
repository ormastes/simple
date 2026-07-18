# Browser App Idle Poll Specification

> <details>

<!-- sdn-diagram:id=browser_app_idle_poll_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_app_idle_poll_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_app_idle_poll_spec -> std
browser_app_idle_poll_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_app_idle_poll_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser App Idle Poll Specification

## Scenarios

### browser app idle file polling

#### throttles idle file change checks but polls immediately after events

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (poll1, ticks1) = browser_file_change_poll_next(false, 0, 3)
expect(poll1).to_equal(false)
expect(ticks1).to_equal(1)

val (poll2, ticks2) = browser_file_change_poll_next(false, ticks1, 3)
expect(poll2).to_equal(false)
expect(ticks2).to_equal(2)

val (poll3, ticks3) = browser_file_change_poll_next(false, ticks2, 3)
expect(poll3).to_equal(true)
expect(ticks3).to_equal(0)

val (poll4, ticks4) = browser_file_change_poll_next(true, 2, 3)
expect(poll4).to_equal(true)
expect(ticks4).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/browser_app_idle_poll_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser app idle file polling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
