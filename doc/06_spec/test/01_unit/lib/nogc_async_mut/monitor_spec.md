# Monitor Specification

> <details>

<!-- sdn-diagram:id=monitor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=monitor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

monitor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=monitor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monitor Specification

## Scenarios

### Monitor stdlib

### exit reason constants

#### EXIT_NORMAL is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EXIT_NORMAL).to_equal("normal")
```

</details>

#### EXIT_KILLED is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EXIT_KILLED).to_equal("killed")
```

</details>

#### EXIT_CRASHED is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EXIT_CRASHED).to_equal("crashed")
```

</details>

#### EXIT_TIMEOUT is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EXIT_TIMEOUT).to_equal("timeout")
```

</details>

### monitor stub

#### returns 0 (stub)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = monitor(42)
expect(ref).to_equal(0)
```

</details>

### down_event

#### creates DownEvent with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = down_event(1, 42, EXIT_NORMAL)
expect(evt.monitor_ref).to_equal(1)
expect(evt.pid).to_equal(42)
expect(evt.reason).to_equal("normal")
```

</details>

#### down_is_normal returns true for normal exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = down_event(1, 42, EXIT_NORMAL)
expect(down_is_normal(evt)).to_equal(true)
```

</details>

#### down_is_normal returns false for crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = down_event(1, 42, EXIT_CRASHED)
expect(down_is_normal(evt)).to_equal(false)
```

</details>

### link_exit_event

#### creates LinkExitEvent with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evt = link_exit_event(99, EXIT_KILLED)
expect(evt.pid).to_equal(99)
expect(evt.reason).to_equal("killed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/monitor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Monitor stdlib
- exit reason constants
- monitor stub
- down_event
- link_exit_event

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
