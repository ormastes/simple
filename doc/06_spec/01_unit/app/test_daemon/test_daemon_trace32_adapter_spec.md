# TRACE32 Adapter Specification

> Tests for the configurable Trace32Adapter in the test daemon. Validates config construction (defaults, map-based, overrides), session key generation, endpoint parsing, and executable selection.

<!-- sdn-diagram:id=test_daemon_trace32_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_trace32_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_trace32_adapter_spec -> std
test_daemon_trace32_adapter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_trace32_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TRACE32 Adapter Specification

Tests for the configurable Trace32Adapter in the test daemon. Validates config construction (defaults, map-based, overrides), session key generation, endpoint parsing, and executable selection.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-ADAPTER |
| Category | Testing |
| Difficulty | 3/5 |
| Status | Implemented |
| Design | doc/05_design/t32_terminal_power_remote.md |
| Source | `test/01_unit/app/test_daemon/test_daemon_trace32_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the configurable Trace32Adapter in the test daemon. Validates
config construction (defaults, map-based, overrides), session key generation,
endpoint parsing, and executable selection.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Trace32AdapterConfig | Configurable struct for T32 adapter settings |
| trace32_adapter_config_from_map | Factory from SDN string map |
| Trace32Client | Proper RCL protocol client (replaces raw netcat) |

## Scenarios

### Trace32AdapterConfig defaults

#### has correct default host

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.t32_host).to_equal("localhost")
```

</details>

#### has correct default RCL port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.rcl_port).to_equal(20000)
```

</details>

#### has correct default install dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.t32_install_dir).to_equal("/opt/t32")
```

</details>

#### has correct default startup wait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.startup_wait_ms).to_equal(3000)
```

</details>

#### has correct default max retries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.max_retries).to_equal(15)
```

</details>

#### has correct default retry interval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.retry_interval_ms).to_equal(500)
```

</details>

#### has correct default reset settle time

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.reset_settle_ms).to_equal(1000)
```

</details>

#### has correct default flash settle time

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.flash_settle_ms).to_equal(1000)
```

</details>

#### has empty default practice script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.practice_script).to_equal("")
```

</details>

#### defaults to exclusive_reused reuse mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.reuse_mode).to_equal(REUSE_EXCLUSIVE_REUSED)
```

</details>

#### defaults to reload_binary reset policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = trace32_adapter_config_default()
expect(cfg.reset_policy).to_equal(RESET_RELOAD_BINARY)
```

</details>

### Trace32AdapterConfig from map

#### overrides host from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["t32_host"] = "192.168.1.50"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.t32_host).to_equal("192.168.1.50")
```

</details>

#### overrides rcl_port from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["rcl_port"] = "20001"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.rcl_port).to_equal(20001)
```

</details>

#### overrides install dir from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["t32_install_dir"] = "/usr/local/t32"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.t32_install_dir).to_equal("/usr/local/t32")
```

</details>

#### overrides startup_wait_ms from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["startup_wait_ms"] = "1500"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.startup_wait_ms).to_equal(1500)
```

</details>

#### overrides max_retries from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["max_retries"] = "8"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.max_retries).to_equal(8)
```

</details>

#### overrides practice_script from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["practice_script"] = "config/t32/startup.cmm"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.practice_script).to_equal("config/t32/startup.cmm")
```

</details>

#### overrides reuse_mode from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["reuse_mode"] = "shared_with_reset"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.reuse_mode).to_equal(REUSE_SHARED_WITH_RESET)
```

</details>

#### overrides reset_policy from map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["reset_policy"] = "hard_reset"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.reset_policy).to_equal(RESET_HARD)
```

</details>

#### falls back to defaults for missing keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["t32_host"] = "10.0.0.1"
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.rcl_port).to_equal(20000)
expect(cfg.t32_install_dir).to_equal("/opt/t32")
expect(cfg.startup_wait_ms).to_equal(3000)
```

</details>

#### handles empty map as all defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
val cfg = trace32_adapter_config_from_map(m)
expect(cfg.t32_host).to_equal("localhost")
expect(cfg.rcl_port).to_equal(20000)
```

</details>

### Trace32Adapter construction

#### creates with defaults via trace32_adapter_new

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
expect(adapter.cfg.rcl_port).to_equal(20000)
expect(adapter.cfg.t32_host).to_equal("localhost")
```

</details>

#### creates with custom config via trace32_adapter_with_config

1. var cfg = trace32 adapter config default
   - Expected: adapter.cfg.t32_host equals `10.0.0.5`
   - Expected: adapter.cfg.rcl_port equals `20002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = trace32_adapter_config_default()
cfg = Trace32AdapterConfig(
    t32_host: "10.0.0.5",
    rcl_port: 20002,
    t32_install_dir: cfg.t32_install_dir,
    startup_wait_ms: cfg.startup_wait_ms,
    max_retries: cfg.max_retries,
    retry_interval_ms: cfg.retry_interval_ms,
    reset_settle_ms: cfg.reset_settle_ms,
    flash_settle_ms: cfg.flash_settle_ms,
    practice_script: cfg.practice_script,
    reuse_mode: cfg.reuse_mode,
    reset_policy: cfg.reset_policy
)
val adapter = trace32_adapter_with_config(cfg)
expect(adapter.cfg.t32_host).to_equal("10.0.0.5")
expect(adapter.cfg.rcl_port).to_equal(20002)
```

</details>

#### creates from map via trace32_adapter_from_map

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["t32_host"] = "192.168.1.100"
m["rcl_port"] = "20010"
m["startup_wait_ms"] = "2000"
val adapter = trace32_adapter_from_map(m)
expect(adapter.cfg.t32_host).to_equal("192.168.1.100")
expect(adapter.cfg.rcl_port).to_equal(20010)
expect(adapter.cfg.startup_wait_ms).to_equal(2000)
```

</details>

### Trace32Adapter session key

#### uses configured reuse_mode in session key

1. var meta = test session meta default
   - Expected: key.reuse_mode equals `REUSE_SHARED_WITH_RESET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["reuse_mode"] = "shared_with_reset"
val adapter = trace32_adapter_from_map(m)
var meta = test_session_meta_default("test.spl")
meta = TestSessionMeta(
    file_path: meta.file_path,
    session_kind: SESSION_KIND_TRACE32,
    target: "stm32h7",
    reuse_mode: meta.reuse_mode,
    reset_policy: meta.reset_policy,
    artifact: "firmware.elf",
    startup_cmd: meta.startup_cmd,
    healthcheck: meta.healthcheck
)
val key = adapter.session_key(meta)
expect(key.reuse_mode).to_equal(REUSE_SHARED_WITH_RESET)
```

</details>

#### uses configured reset_policy in session key

1. var meta = test session meta default
   - Expected: key.reset_policy equals `RESET_HARD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m: {text: text} = {}
m["reset_policy"] = "hard_reset"
val adapter = trace32_adapter_from_map(m)
var meta = test_session_meta_default("test.spl")
meta = TestSessionMeta(
    file_path: meta.file_path,
    session_kind: SESSION_KIND_TRACE32,
    target: "cortex-m4",
    reuse_mode: meta.reuse_mode,
    reset_policy: meta.reset_policy,
    artifact: "",
    startup_cmd: meta.startup_cmd,
    healthcheck: meta.healthcheck
)
val key = adapter.session_key(meta)
expect(key.reset_policy).to_equal(RESET_HARD)
```

</details>

#### can_handle returns true for TRACE32 sessions

1. var meta = test session meta default
   - Expected: adapter.can_handle(meta) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
var meta = test_session_meta_default("test.spl")
meta = TestSessionMeta(
    file_path: meta.file_path,
    session_kind: SESSION_KIND_TRACE32,
    target: "arm",
    reuse_mode: meta.reuse_mode,
    reset_policy: meta.reset_policy,
    artifact: meta.artifact,
    startup_cmd: meta.startup_cmd,
    healthcheck: meta.healthcheck
)
expect(adapter.can_handle(meta)).to_equal(true)
```

</details>

#### can_handle returns false for non-TRACE32 sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val meta = test_session_meta_default("test.spl")
expect(adapter.can_handle(meta)).to_equal(false)
```

</details>

### Trace32Adapter target executable

#### selects t32marm for ARM targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("cortex-m4")
expect(exe).to_equal("t32marm")
```

</details>

#### selects t32marm for arm keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("arm-none-eabi")
expect(exe).to_equal("t32marm")
```

</details>

#### selects t32mriscv for RISC-V targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("rv32imac")
expect(exe).to_equal("t32mriscv")
```

</details>

#### selects t32mriscv for riscv keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("riscv64")
expect(exe).to_equal("t32mriscv")
```

</details>

#### selects t32mx86 for x86 targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("x86_64")
expect(exe).to_equal("t32mx86")
```

</details>

#### selects t32mppc for PowerPC targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("powerpc-e500")
expect(exe).to_equal("t32mppc")
```

</details>

#### defaults to t32marm for unknown targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val exe = adapter.t32_executable_for_target("unknown-target")
expect(exe).to_equal("t32marm")
```

</details>

### Trace32Adapter endpoint parsing

#### parses host:port correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val ep = adapter.parse_endpoint("192.168.1.50:20001")
expect(ep.host).to_equal("192.168.1.50")
expect(ep.port).to_equal(20001)
```

</details>

#### parses localhost:20000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val ep = adapter.parse_endpoint("localhost:20000")
expect(ep.host).to_equal("localhost")
expect(ep.port).to_equal(20000)
```

</details>

#### falls back to config defaults for malformed input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = trace32_adapter_new()
val ep = adapter.parse_endpoint("no-port-here")
expect(ep.host).to_equal("localhost")
expect(ep.port).to_equal(20000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/t32_terminal_power_remote.md](doc/05_design/t32_terminal_power_remote.md)


</details>
