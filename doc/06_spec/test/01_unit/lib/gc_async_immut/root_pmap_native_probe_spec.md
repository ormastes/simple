# Root Pmap Native Probe Specification

> 1. expect pmap

<!-- sdn-diagram:id=root_pmap_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=root_pmap_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

root_pmap_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=root_pmap_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Root Pmap Native Probe Specification

## Scenarios

### gc_async_immut root pmap native probe

#### runs pmap from the root facade

1. expect pmap


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect pmap([1, 2, 3], _1 + 1) == [2, 3, 4]
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/root_pmap_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut root pmap native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
