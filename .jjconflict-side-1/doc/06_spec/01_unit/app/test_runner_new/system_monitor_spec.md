# System Monitor Specification

> <details>

<!-- sdn-diagram:id=system_monitor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=system_monitor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

system_monitor_spec -> std
system_monitor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=system_monitor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Monitor Specification

## Scenarios

### System Monitor

#### detects platform flags as booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linux = is_linux()
val macos = is_macos()
val windows = is_windows()
val freebsd = is_freebsd()

expect(linux == true or linux == false).to_equal(true)
expect(macos == true or macos == false).to_equal(true)
expect(windows == true or windows == false).to_equal(true)
expect(freebsd == true or freebsd == false).to_equal(true)
```

</details>

#### returns non-negative system resource metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = get_system_resources()

expect(res.cpu_percent >= 0.0).to_equal(true)
expect(res.memory_percent >= 0.0).to_equal(true)
expect(res.memory_used_mb >= 0).to_equal(true)
expect(res.memory_total_mb >= 0).to_equal(true)

if res.memory_total_mb > 0:
    expect(res.memory_used_mb <= res.memory_total_mb).to_equal(true)
```

</details>

#### returns cpu and memory percentages directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = get_system_cpu_percent()
val memory = get_system_memory_percent()

expect(cpu >= 0.0).to_equal(true)
expect(memory >= 0.0).to_equal(true)
```

</details>

#### only reports threshold violations when both limits are exceeded

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (safe, safe_reason) = system_exceeds_threshold(101.0, 101.0)
val (violated, violated_reason) = system_exceeds_threshold(-1.0, -1.0)

expect(safe).to_equal(false)
expect(safe_reason).to_equal("")
expect(violated).to_equal(true)
expect(violated_reason != "").to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/system_monitor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- System Monitor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
