# Pressure Vessel Specification

> <details>

<!-- sdn-diagram:id=pressure_vessel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pressure_vessel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pressure_vessel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pressure_vessel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pressure Vessel Specification

## Scenarios

### Pressure-vessel container

#### create with valid rootfs returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/var/lib/pressure-vessel/runtime", true)
expect(result.is_ok).to_equal(true)
expect(result.container_id).to_be_greater_than(0)
expect(result.status).to_equal("created")
```

</details>

#### create with empty rootfs returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("", true)
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("missing-rootfs-path")
```

</details>

#### has_nvfs returns true when NVFS backend requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", true)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(true)
```

</details>

#### has_nvfs returns false when NVFS backend not requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", false)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(false)
```

</details>

#### has_nvfs returns false for invalid container

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pressure_vessel_has_nvfs(0)).to_equal(false)
```

</details>

#### namespace_profile contains all five facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", true)
val profile = pressure_vessel_namespace_profile(result.container_id)
expect(profile).to_contain("ns-pid")
expect(profile).to_contain("ns-fs")
expect(profile).to_contain("ns-ipc")
expect(profile).to_contain("ns-net")
expect(profile).to_contain("ns-capability")
```

</details>

#### exec with valid command returns exec-ready status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", true)
val exec = pressure_vessel_exec(result.container_id, "wine64 hl2.exe")
expect(exec.is_ok).to_equal(true)
expect(exec.status).to_equal("exec-ready")
```

</details>

#### exec with empty command returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", true)
val exec = pressure_vessel_exec(result.container_id, "")
expect(exec.is_ok).to_equal(false)
expect(exec.error).to_equal("missing-command")
```

</details>

#### exec on invalid container returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exec = pressure_vessel_exec(0, "wine64 app.exe")
expect(exec.is_ok).to_equal(false)
```

</details>

#### destroy makes container unreachable

1. pressure vessel destroy
   - Expected: pressure_vessel_has_nvfs(result.container_id) is false
   - Expected: profile equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pressure_vessel_create("/rootfs", true)
pressure_vessel_destroy(result.container_id)
expect(pressure_vessel_has_nvfs(result.container_id)).to_equal(false)
val profile = pressure_vessel_namespace_profile(result.container_id)
expect(profile).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/container/pressure_vessel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pressure-vessel container

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
