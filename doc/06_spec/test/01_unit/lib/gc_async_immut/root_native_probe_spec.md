# Root Native Probe Specification

> 1. expect pmap

<!-- sdn-diagram:id=root_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=root_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

root_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=root_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Root Native Probe Specification

## Scenarios

### gc_async_immut root native probe

#### runs root helpers

1. expect pmap
2. expect nogc async immut version


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pmap([1, 2, 3], _1 + 1) == [2, 3, 4]
expect nogc_async_immut_version() == "0.1.0"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/root_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut root native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
