# Storage Init Facade Specification

> <details>

<!-- sdn-diagram:id=storage_init_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_init_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_init_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_init_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Init Facade Specification

## Scenarios

### nogc_async_mut storage package facade

#### re-exports storage leaf symbols from the package namespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(StorageClass.DB_TEMP.to_string()).to_equal("DB_TEMP")
expect(DurabilityClass.Flush.to_string()).to_equal("Flush")
expect(ArenaHandle.null().is_null()).to_equal(true)
expect(STORAGE_CLASS_DB_WAL).to_equal(1)
val policy = nvme_policy_for_class(samsung_mzql2960hcjr_sysfs_facts(), StorageClass.DB_WAL)
expect(policy.backend).to_equal("conventional-nvme")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/storage/storage_init_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut storage package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
