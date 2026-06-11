# Proton Real Exec Specification

> <details>

<!-- sdn-diagram:id=proton_real_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proton_real_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proton_real_exec_spec -> common
proton_real_exec_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proton_real_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Real Exec Specification

## Scenarios

### Proton real execution via pressure-vessel

#### dry_run=true still returns dry-run-ready (regression)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

#### dry_run=false no longer returns execution-not-implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.error).to_equal("")
expect(handoff.status != "blocked").to_equal(true)
```

</details>

#### dry_run=false returns exec-dispatched status

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("exec-dispatched")
```

</details>

#### dry_run=false launch_command contains wine64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", ["-novid"])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.launch_command).to_contain("wine64")
expect(handoff.launch_command).to_contain("hl2.exe")
```

</details>

#### container_profile contains namespace facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "steamapps/compatdata/480/pfx", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.container_profile).to_contain("ns-pid")
expect(handoff.container_profile).to_contain("ns-fs")
expect(handoff.container_profile).to_contain("ns-capability")
```

</details>

#### invalid plan returns error for both dry_run modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("", "steamapps/compatdata/480/pfx", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val dry = proton_session_launch_handoff(plan, true)
expect(dry.ok).to_equal(false)
expect(dry.status).to_equal("blocked")
val real = proton_session_launch_handoff(plan, false)
expect(real.ok).to_equal(false)
expect(real.status).to_equal("blocked")
```

</details>

#### missing compat_prefix returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = proton_session_request_new("480", "", "hl2.exe", [])
val plan = proton_session_plan(request, proton_fixture_non_wine_runtime_evidence())
val handoff = proton_session_launch_handoff(plan, false)
expect(handoff.ok).to_equal(false)
expect(handoff.error).to_equal("missing-compat-prefix")
```

</details>

#### pressure_vessel_exec_wine composes wine command

1. pressure vessel destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container = pressure_vessel_create("/tmp/rootfs", true)
expect(container.is_ok).to_equal(true)
val result = pressure_vessel_exec_wine(container.container_id, "game.exe")
expect(result.is_ok).to_equal(true)
expect(result.status).to_equal("exec-ready")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_exec_wine fails with empty executable

1. pressure vessel destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_exec_wine(container.container_id, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-executable")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_setup_wine_prefix succeeds with valid path

1. pressure vessel destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_setup_wine_prefix(container.container_id, "/tmp/wine-prefix")
expect(result.is_ok).to_equal(true)
expect(result.status).to_equal("prefix-ready")
pressure_vessel_destroy(container.container_id)
```

</details>

#### pressure_vessel_setup_wine_prefix fails with empty path

1. pressure vessel destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container = pressure_vessel_create("/tmp/rootfs", true)
val result = pressure_vessel_setup_wine_prefix(container.container_id, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-prefix-path")
pressure_vessel_destroy(container.container_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/proton_real_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Proton real execution via pressure-vessel

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
