# Vector Empty Native Probe Specification

> <details>

<!-- sdn-diagram:id=vector_empty_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vector_empty_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vector_empty_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vector_empty_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vector Empty Native Probe Specification

## Scenarios

### gc_async_immut vector empty native probe

#### constructs an empty vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = PersistentVec.empty()
expect(base.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/vector_empty_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut vector empty native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
