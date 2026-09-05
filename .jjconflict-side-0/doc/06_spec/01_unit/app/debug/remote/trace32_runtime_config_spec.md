# Trace32 Runtime Config Specification

> <details>

<!-- sdn-diagram:id=trace32_runtime_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trace32_runtime_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trace32_runtime_config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trace32_runtime_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trace32 Runtime Config Specification

## Scenarios

### Trace32 runtime command config

#### builds a basic t32rem command without protocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = Trace32Client.build_command(
    "/opt/t32/bin/pc_linux64/t32rem", "localhost", 20000, "", "PING"
)
expect(cmd).to_equal("/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING")
```

</details>

#### includes protocol override when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = Trace32Client.build_command(
    "/opt/t32/bin/pc_linux64/t32rem", "localhost", 20000, "NETASSIST", "PING"
)
expect(cmd).to_equal("/opt/t32/bin/pc_linux64/t32rem localhost port=20000 protocol=NETASSIST PING")
```

</details>

#### supports wrapper scripts as the executable path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = Trace32Client.build_command(
    "scripts/t32rem_docker.shs", "localhost", 20000, "NETTCP",
    "SETUP.API.GDB.Enable /PORT 2331"
)
expect(cmd).to_start_with("scripts/t32rem_docker.shs localhost port=20000 protocol=NETTCP")
expect(cmd).to_end_with("SETUP.API.GDB.Enable /PORT 2331")
```

</details>

### Trace32 wait timing

#### uses at least one second for zero timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Trace32Client.wait_seconds(0)).to_equal(1)
```

</details>

#### rounds sub-second waits up to one second

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Trace32Client.wait_seconds(500)).to_equal(1)
```

</details>

#### uses whole seconds for larger waits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Trace32Client.wait_seconds(5000)).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/trace32_runtime_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Trace32 runtime command config
- Trace32 wait timing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
