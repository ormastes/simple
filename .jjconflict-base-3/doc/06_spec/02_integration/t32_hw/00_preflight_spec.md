# 00 Preflight Specification

> <details>

<!-- sdn-diagram:id=00_preflight_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=00_preflight_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

00_preflight_spec -> std
00_preflight_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=00_preflight_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# 00 Preflight Specification

## Scenarios

### T32 hardware preflight

#### tool availability

#### detects T32 installation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = t32_hw_t32rem_available()
expect(available).to_equal(true)
```

</details>

#### T32 RCL port is reachable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reachable = t32_hw_probe_available()
expect(reachable).to_equal(true)
```

</details>

#### version checks

#### queries T32 version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = t32_hw_query_version()
expect(version).to_be_greater_than(0)
```

</details>

#### version meets OLD tool minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = t32_hw_query_version()
expect(version).to_be_greater_than(T32_HW_MIN_VERSION_OLD - 1)
```

</details>

#### relay infrastructure

#### relay scripts accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = t32_hw_relay_available()
expect(available).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/t32_hw/00_preflight_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 hardware preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
