# Tmp Harness Probe Specification

> <details>

<!-- sdn-diagram:id=_tmp_harness_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_tmp_harness_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_tmp_harness_probe_spec -> std
_tmp_harness_probe_spec -> os
_tmp_harness_probe_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_tmp_harness_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Harness Probe Specification

## Scenarios

### tmp harness probe

#### allocates a live host port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = allocate_live_host_port(32000)
expect(result.is_ok()).to_equal(true)
```

</details>

#### spawns the guest with unique resources

1. dir create all
   - Expected: spawn_result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port_result = allocate_live_host_port(32100)
expect(port_result.is_ok()).to_equal(true)
if port_result.is_ok():
    val port = port_result.unwrap()
    val target = get_ssh_live_target()
    val scenario = _scenario_x64_ssh_on_port(port)
    expect(build_os_with_backend(target, "cranelift")).to_equal(true)
    expect(can_run_target(target)).to_equal(true)
    expect(ensure_scenario_media(scenario)).to_equal(true)
    dir_create_all("build/os")
    val token = "{rt_getpid()}_{rt_time_now_unix_micros()}"
    val qmp_socket = "/tmp/harness_probe_{token}.sock"
    val serial_log = "build/os/harness_probe_{token}.log"
    val spawn_result = spawn_guest_with_qmp_scenario(target, scenario, qmp_socket, serial_log)
    expect(spawn_result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/_tmp_harness_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmp harness probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
