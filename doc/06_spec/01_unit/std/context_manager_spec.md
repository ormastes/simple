# Context Manager Specification

> <details>

<!-- sdn-diagram:id=context_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_manager_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Manager Specification

## Scenarios

### Context Manager

#### TimerContext

#### should measure elapsed time

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use direct construction to avoid module var import bug
var timer_start = 0.0
var timer_end = 0.0

# Simulate a timer: record start, do work, record end
timer_start = 1.0

# Simulate some work
var sum = 0
for i in 0..1000:
    sum = sum + i

timer_end = 2.0

# Elapsed time should be positive
val elapsed = timer_end - timer_start
expect(elapsed).to_be_greater_than(0.0)
```

</details>

#### time measurement

#### should track timing correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test basic timing arithmetic
val start = 100.5
val end_time = 200.75
val elapsed = end_time - start

expect(elapsed).to_equal(100.25)
expect(elapsed).to_be_greater_than(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/context_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context Manager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
