# Dbfs Driver Facade Specification

> <details>

<!-- sdn-diagram:id=dbfs_driver_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_driver_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_driver_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_driver_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Driver Facade Specification

## Scenarios

### gc_async_mut DBFS driver facade

#### constructs the canonical DBFS hosted driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = DbFsDriver.new_hosted()
expect(driver.preferred_io_unit_bytes()).to_equal(512)
expect(driver.preferred_batch_bytes()).to_equal(4096)
expect(driver.has_trim_support()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_driver/dbfs_driver_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DBFS driver facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
