# Versioned Native Probe Specification

> 1. var snapshot = VersionedSnapshot new

<!-- sdn-diagram:id=versioned_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=versioned_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

versioned_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=versioned_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Versioned Native Probe Specification

## Scenarios

### gc_async_immut versioned native probe

#### constructs a snapshot

1. var snapshot = VersionedSnapshot new
2. expect snapshot current


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snapshot = VersionedSnapshot.new("old")
expect snapshot.current() == "old"
```

</details>

#### updates a snapshot

1. var snapshot = VersionedSnapshot new
2. snapshot update
3. expect snapshot current


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var snapshot = VersionedSnapshot.new("old")
snapshot.update("new")
expect snapshot.current() == "new"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_immut/versioned_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_immut versioned native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
