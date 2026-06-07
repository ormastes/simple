# Dbfs Driver Init Facade Specification

> <details>

<!-- sdn-diagram:id=dbfs_driver_init_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_driver_init_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_driver_init_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_driver_init_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Driver Init Facade Specification

## Scenarios

### nogc_async_mut DBFS driver package facade

#### re-exports DbFsDriver from the package namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = DbFsDriver.new_hosted()
expect(driver.preferred_batch_bytes()).to_equal(4096)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_driver/dbfs_driver_init_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut DBFS driver package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
