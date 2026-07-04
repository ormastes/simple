# Time Ops Unix Specification

> <details>

<!-- sdn-diagram:id=time_ops_unix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=time_ops_unix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

time_ops_unix_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=time_ops_unix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Time Ops Unix Specification

## Scenarios

### app.io.time_ops

### time_now_unix_micros

#### returns positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = time_now_unix_micros()
expect(t).to_be_greater_than(0)
```

</details>

### current_time_unix

#### returns seconds since epoch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = current_time_unix()
expect(t).to_be_greater_than(1700000000)
```

</details>

### current_time_ms

#### returns milliseconds since epoch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = current_time_ms()
expect(t).to_be_greater_than(1700000000000)
```

</details>

### time ordering

#### micros > ms > unix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val micros = time_now_unix_micros()
val ms = current_time_ms()
val unix = current_time_unix()
expect(micros).to_be_greater_than(ms)
expect(ms).to_be_greater_than(unix)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/time_ops_unix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io.time_ops
- time_now_unix_micros
- current_time_unix
- current_time_ms
- time ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
