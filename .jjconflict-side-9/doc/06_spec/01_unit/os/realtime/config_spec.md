# Config Specification

> <details>

<!-- sdn-diagram:id=config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Specification

## Scenarios

### Profile and Probe Constants

#### profile constants are sequential 0-3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TEST_PROFILE_FAST).to_equal(0)
expect(TEST_PROFILE_SESSION).to_equal(1)
expect(TEST_PROFILE_FUZZ).to_equal(2)
expect(TEST_PROFILE_VERIFY).to_equal(3)
```

</details>

#### probe type constants are 0 and 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(JTAG_PROBE_OPENOCD).to_equal(0)
expect(JTAG_PROBE_TRACE32).to_equal(1)
```

</details>

### RtosJtagConfig

#### default_openocd has localhost:3333 with probe_type 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RtosJtagConfig.default_openocd()
expect(cfg.host).to_equal("localhost")
expect(cfg.port).to_equal(3333)
expect(cfg.probe_type).to_equal(0)
expect(cfg.t32_ping_timeout_ms).to_equal(0)
expect(cfg.t32_max_retries).to_equal(0)
expect(cfg.t32_auto_reconnect).to_equal(false)
```

</details>

#### default_trace32 has localhost:20000 with probe_type 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RtosJtagConfig.default_trace32()
expect(cfg.host).to_equal("localhost")
expect(cfg.port).to_equal(20000)
expect(cfg.probe_type).to_equal(1)
```

</details>

#### default_trace32 has correct T32 timeouts and retries

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RtosJtagConfig.default_trace32()
expect(cfg.t32_ping_timeout_ms).to_equal(3000)
expect(cfg.t32_operation_timeout_ms).to_equal(10000)
expect(cfg.t32_max_retries).to_equal(3)
expect(cfg.t32_auto_reconnect).to_equal(true)
expect(cfg.t32_kill_on_hang).to_equal(false)
```

</details>

### RtosTestConfig

#### default_fast has replay off, 5s timeout, no fuzz

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = RtosTestConfig.default_fast()
expect(cfg.replay_mode).to_equal(0)
expect(cfg.timeout_ms).to_equal(5000)
expect(cfg.fuzz_enabled).to_equal(false)
expect(cfg.fuzz_iterations).to_equal(0)
expect(cfg.checkpoint_id).to_equal(0)
```

</details>

### jtag_to_t32_watchdog_config Bridge

#### maps all T32 fields from trace32 defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jtag = RtosJtagConfig.default_trace32()
val wd = jtag_to_t32_watchdog_config(jtag)
expect(wd.ping_timeout_ms).to_equal(3000)
expect(wd.operation_timeout_ms).to_equal(10000)
expect(wd.max_retries).to_equal(3)
expect(wd.auto_reconnect).to_equal(true)
expect(wd.kill_on_hang).to_equal(false)
expect(wd.host).to_equal("localhost")
expect(wd.port).to_equal(20000)
```

</details>

#### maps zeroed fields from openocd defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jtag = RtosJtagConfig.default_openocd()
val wd = jtag_to_t32_watchdog_config(jtag)
expect(wd.ping_timeout_ms).to_equal(0)
expect(wd.max_retries).to_equal(0)
expect(wd.host).to_equal("localhost")
expect(wd.port).to_equal(3333)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/realtime/config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Profile and Probe Constants
- RtosJtagConfig
- RtosTestConfig
- jtag_to_t32_watchdog_config Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
