# Storage Policy Facade Specification

> <details>

<!-- sdn-diagram:id=storage_policy_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_policy_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_policy_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_policy_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Policy Facade Specification

## Scenarios

### nogc_async_mut storage policy facade

#### re-exports storage classes, durability, arena handles, and NVMe policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(StorageClass.DB_WAL.to_string()).to_equal("DB_WAL")
expect(StorageClass.DB_WAL.is_append_only()).to_equal(true)
expect(DurabilityClass.FlushFua.to_string()).to_equal("FlushFua")
val h = ArenaHandle.null()
expect(h.is_null()).to_equal(true)
val req = FlushRequest(arena_id: 7, low_gen: 1, high_gen: 2, durability: DurabilityClass.Flush)
expect(req.high_gen).to_equal(2)
val facts = samsung_mzql2960hcjr_sysfs_facts()
val policy = nvme_policy_for_class(facts, StorageClass.DB_WAL)
expect(policy.io_unit_bytes).to_equal(4096)
expect(policy.batch_bytes).to_equal(131072)
expect(policy.uses_discard).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/storage/storage_policy_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut storage policy facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
