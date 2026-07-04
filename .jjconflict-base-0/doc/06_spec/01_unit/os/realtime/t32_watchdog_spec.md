# T32 Watchdog Specification

> <details>

<!-- sdn-diagram:id=t32_watchdog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_watchdog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_watchdog_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_watchdog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Watchdog Specification

## Scenarios

### State Constants

#### state values are sequential 0-3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_ALIVE).to_equal(0)
expect(T32_SUSPECT).to_equal(1)
expect(T32_HUNG).to_equal(2)
expect(T32_DEAD).to_equal(3)
```

</details>

### T32WatchdogConfig

#### defaults has correct timeouts, retries, and connection info

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
expect(cfg.ping_timeout_ms).to_equal(3000)
expect(cfg.operation_timeout_ms).to_equal(10000)
expect(cfg.max_retries).to_equal(3)
expect(cfg.auto_reconnect).to_equal(true)
expect(cfg.kill_on_hang).to_equal(false)
expect(cfg.host).to_equal("localhost")
expect(cfg.port).to_equal(20000)
```

</details>

### T32Watchdog Construction

#### new starts in ALIVE state, not connected, zero counters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val wd = T32Watchdog.new(cfg)
expect(wd.state).to_equal(T32_ALIVE)
expect(wd.connected).to_equal(false)
expect(wd.consecutive_failures).to_equal(0)
expect(wd.total_hangs).to_equal(0)
expect(wd.total_recoveries).to_equal(0)
```

</details>

### T32Watchdog State Queries

#### is_alive true only in ALIVE state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val wd = T32Watchdog.new(cfg)
expect(wd.is_alive()).to_equal(true)
expect(wd.is_hung()).to_equal(false)
```

</details>

#### is_alive false in SUSPECT state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val suspect = T32Watchdog(
    config: cfg, state: T32_SUSPECT,
    consecutive_failures: 1, total_hangs: 0,
    total_recoveries: 0, connected: true
)
expect(suspect.is_alive()).to_equal(false)
expect(suspect.is_hung()).to_equal(false)
```

</details>

#### is_hung true only in HUNG state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val hung = T32Watchdog(
    config: cfg, state: T32_HUNG,
    consecutive_failures: 3, total_hangs: 1,
    total_recoveries: 0, connected: true
)
expect(hung.is_hung()).to_equal(true)
expect(hung.is_alive()).to_equal(false)
```

</details>

### T32Watchdog State Transitions

#### SUSPECT after fewer than max_retries failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val suspect = T32Watchdog(
    config: cfg, state: T32_SUSPECT,
    consecutive_failures: 2, total_hangs: 0,
    total_recoveries: 0, connected: true
)
expect(suspect.state).to_equal(T32_SUSPECT)
expect(suspect.consecutive_failures).to_be_less_than(3)
```

</details>

#### HUNG when consecutive_failures reaches max_retries

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val hung = T32Watchdog(
    config: cfg, state: T32_HUNG,
    consecutive_failures: 3, total_hangs: 1,
    total_recoveries: 0, connected: true
)
expect(hung.state).to_equal(T32_HUNG)
expect(hung.consecutive_failures).to_equal(cfg.max_retries)
expect(hung.total_hangs).to_equal(1)
```

</details>

### T32Watchdog Stats

#### stats_text contains hang and recovery counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val wd = T32Watchdog.new(cfg)
expect(wd.stats_text()).to_contain("hangs=0")
expect(wd.stats_text()).to_contain("recoveries=0")
expect(wd.stats_text()).to_contain("state=0")
```

</details>

#### stats_text reflects accumulated hangs and recoveries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = T32WatchdogConfig.defaults()
val hung = T32Watchdog(
    config: cfg, state: T32_HUNG, consecutive_failures: 3,
    total_hangs: 2, total_recoveries: 1, connected: true
)
expect(hung.stats_text()).to_contain("hangs=2")
expect(hung.stats_text()).to_contain("recoveries=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/t32_watchdog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- State Constants
- T32WatchdogConfig
- T32Watchdog Construction
- T32Watchdog State Queries
- T32Watchdog State Transitions
- T32Watchdog Stats

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
