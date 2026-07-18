# Samsung Nvme Feature Policy Specification

> <details>

<!-- sdn-diagram:id=samsung_nvme_feature_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=samsung_nvme_feature_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

samsung_nvme_feature_policy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=samsung_nvme_feature_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Samsung Nvme Feature Policy Specification

## Scenarios

### Samsung business NVMe feature policy

#### uses the conventional NVMe path for the attached MZQL2960HCJR namespace

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = samsung_mzql2960hcjr_sysfs_facts()
val wal = nvme_policy_for_class(facts, StorageClass.DB_WAL)
expect(wal.backend).to_equal("conventional-nvme")
expect(wal.io_unit_bytes).to_equal(4096)
expect(wal.batch_bytes).to_equal(131072)
expect(wal.uses_discard).to_equal(true)
expect(wal.uses_write_zeroes).to_equal(true)
```

</details>

#### does not claim FDP or ZNS when sysfs reports no zone append path

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = samsung_mzql2960hcjr_sysfs_facts()
val summary = nvme_policy_summary(facts)
expect(summary.contains("conventional")).to_equal(true)
expect(summary.contains("no-fdp")).to_equal(true)
```

</details>

#### keeps distinct placement IDs for DBFS/NVFS storage classes

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val facts = samsung_mzql2960hcjr_sysfs_facts()
val meta = nvme_policy_for_class(facts, StorageClass.META_DURABLE)
val wal = nvme_policy_for_class(facts, StorageClass.DB_WAL)
val temp = nvme_policy_for_class(facts, StorageClass.DB_TEMP)
expect(meta.placement_id != wal.placement_id).to_equal(true)
expect(wal.placement_id != temp.placement_id).to_equal(true)
```

</details>

#### wires Samsung policy into DBFS device construction

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = RamBlockDevice.new_empty()
val opened = DbFsDriver.open_on_samsung_business_nvme(dev, 0, 1024)
expect(opened.is_ok()).to_equal(true)
val dbfs = opened.unwrap()
expect(dbfs.preferred_io_unit_bytes()).to_equal(4096)
expect(dbfs.preferred_batch_bytes()).to_equal(131072)
expect(dbfs.has_trim_support()).to_equal(true)
expect(dbfs.has_write_zeroes_support()).to_equal(true)
```

</details>

#### wires Samsung policy into NVFS native construction

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvfs = NvfsDriver.new_samsung_business_nvme("nvfs-samsung")
expect(nvfs.preferred_io_unit_bytes()).to_equal(4096)
expect(nvfs.preferred_batch_bytes()).to_equal(4096)
expect(nvfs.has_trim_support()).to_equal(true)
expect(nvfs.has_write_zeroes_support()).to_equal(true)
```

</details>

### DBFS/NVFS/FAT32 benchmark order

#### models NVFS lower work than FAT32 on Samsung conventional NVMe

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files: i64 = 256
val blocks: i64 = 4096
val fat = fat32_cost(files, blocks)
val nvfs = nvfs_cost(files, blocks)
expect(nvfs.total() < fat.total()).to_equal(true)
```

</details>

#### models DBFS lower work than NVFS through WAL group commit and class placement

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files: i64 = 256
val blocks: i64 = 4096
val nvfs = nvfs_cost(files, blocks)
val dbfs = dbfs_cost(files, blocks)
expect(dbfs.total() < nvfs.total()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/samsung_nvme_feature_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Samsung business NVMe feature policy
- DBFS/NVFS/FAT32 benchmark order

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
