# Duplicate Check Debug Helpers Specification

> Tests the debug flag helpers used by the duplicate detection tool. The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide throttled progress logging.

<!-- sdn-diagram:id=duplicate_check_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=duplicate_check_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

duplicate_check_debug_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=duplicate_check_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Debug Helpers Specification

Tests the debug flag helpers used by the duplicate detection tool. The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide throttled progress logging.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/duplicate_check_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the debug flag helpers used by the duplicate detection tool.
The helpers read `SIMPLE_DUP_DEBUG` env var on demand and provide
throttled progress logging.

## Key Concepts

| Concept         | Description                                      |
|-----------------|--------------------------------------------------|
| get_debug_flag  | Returns true when SIMPLE_DUP_DEBUG is "1"/"true" |
| debug_log       | Emits message only when tracing is on            |
| debug_log_progress | Throttles output to every 10th step           |

## Scenarios

### Duplicate Check Debug Flag

#### get_debug_flag returns bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = get_debug_flag()
expect(flag == true or flag == false).to_equal(true)
```

</details>

#### get_debug_flag defaults to false when env unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = get_debug_flag()
expect(flag).to_equal(false)
```

</details>

### Duplicate Check Debug Functions

#### init_debug does not error

1. init debug
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_debug()
expect(get_debug_flag()).to_equal(false)
```

</details>

#### debug_log does not error when debug is off

1. debug log
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log("test message")
expect(get_debug_flag()).to_equal(false)
```

</details>

#### debug_log_progress does not error when debug is off

1. debug log progress
2. debug log progress
3. debug log progress
   - Expected: get_debug_flag() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_log_progress(0, 10, "scanning")
debug_log_progress(5, 10, "scanning")
debug_log_progress(10, 10, "scanning")
expect(get_debug_flag()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
