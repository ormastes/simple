# Boot Fs Mount Acceptance Specification

> 1. boot fs mount clear production nvme lease device

<!-- sdn-diagram:id=boot_fs_mount_acceptance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_fs_mount_acceptance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_fs_mount_acceptance_spec -> std
boot_fs_mount_acceptance_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_fs_mount_acceptance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Fs Mount Acceptance Specification

## Scenarios

### boot filesystem mount acceptance

#### default and production freestanding entries require provisioned pure NVMe lease device

1. boot fs mount clear production nvme lease device
   - Expected: default_rejected.is_err() is true
   - Expected: default_rejected.unwrap_err() equals `boot-fs-mount: pure-nvme-production-device-not-provisioned`
   - Expected: rejected.is_err() is true
   - Expected: rejected.unwrap_err() equals `boot-fs-mount: pure-nvme-production-device-not-provisioned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_fs_mount_clear_production_nvme_lease_device()
val default_rejected = boot_fs_mount_freestanding()
expect(default_rejected.is_err()).to_equal(true)
expect(default_rejected.unwrap_err()).to_equal("boot-fs-mount: pure-nvme-production-device-not-provisioned")

val rejected = boot_fs_mount_freestanding_production()
expect(rejected.is_err()).to_equal(true)
expect(rejected.unwrap_err()).to_equal("boot-fs-mount: pure-nvme-production-device-not-provisioned")
```

</details>

#### rejects C bridge mounts as pure Simple boot storage

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_bridge = FsMountResult(
    mounted: true,
    fs_type: FsMountType.Nvfs,
    provider: "c-boot-bridge",
    pure_simple: false
)
val evidence = boot_storage_acceptance_evidence(
    c_bridge,
    true,
    true,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    true
)
expect(boot_fs_mount_acceptance_reason(c_bridge)).to_equal("boot-storage-not-pure-simple:c-boot-bridge")
expect(boot_fs_mount_provider_is_pure_simple("c-boot-bridge")).to_equal(false)
expect(boot_fs_mount_provider_is_pure_simple("simple-driver")).to_equal(true)
expect(boot_storage_acceptance_ready(evidence)).to_equal(false)
expect(boot_storage_acceptance_reason(evidence)).to_equal("boot-storage-not-pure-simple:c-boot-bridge")
```

</details>

#### requires PCI grants, transfers, sector probe, and non-secure namespace

1. simple nvfs result
   - Expected: boot_storage_acceptance_reason(missing_grant) equals `missing-boot-storage-pci-grant`
2. simple nvfs result
   - Expected: boot_storage_acceptance_reason(missing_transfer) equals `missing-boot-storage-transfer`
3. simple nvfs result
   - Expected: boot_storage_acceptance_reason(missing_probe) equals `missing-real-sector-superblock-probe`
4. simple nvfs result
   - Expected: boot_storage_acceptance_reason(secure_namespace) equals `missing-boot-storage-non-secure-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_grant = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    false,
    true,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    true
)
expect(boot_storage_acceptance_reason(missing_grant)).to_equal("missing-boot-storage-pci-grant")

val missing_transfer = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    false,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    true
)
expect(boot_storage_acceptance_reason(missing_transfer)).to_equal("missing-boot-storage-transfer")

val missing_probe = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    false,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    true
)
expect(boot_storage_acceptance_reason(missing_probe)).to_equal("missing-real-sector-superblock-probe")

val secure_namespace = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    true,
    false,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    true
)
expect(boot_storage_acceptance_reason(secure_namespace)).to_equal("missing-boot-storage-non-secure-namespace")
```

</details>

#### requires direct-access grant placement shared logic and broker evidence

1. simple nvfs result
2. simple nvfs result
3. simple nvfs result
4. simple nvfs result


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokenless_grant = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    true,
    true,
    "raw-device-grant",
    "user-space-driver",
    true,
    true
)
expect(boot_storage_acceptance_reason(tokenless_grant)).to_contain("missing-issued-device-grant-token:raw-device-grant")

val kernel_placement = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "kernel",
    true,
    true
)
expect(boot_storage_acceptance_reason(kernel_placement)).to_contain("direct-access-not-user-space-driver:kernel")

val missing_common_logic = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    false,
    true
)
expect(boot_storage_acceptance_reason(missing_common_logic)).to_contain("missing-common-driver-logic")

val missing_broker = boot_storage_acceptance_evidence(
    simple_nvfs_result(),
    true,
    true,
    true,
    true,
    "raw-device-grant:tok=boot-nvme",
    "user-space-driver",
    true,
    false
)
expect(boot_storage_acceptance_reason(missing_broker)).to_contain("missing-iommu-or-grant-broker")
```

</details>

#### accepts NVFS DBFS and FAT32 only after the full Simple evidence set

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nvfs = ready_boot_storage_evidence(simple_nvfs_result())
expect(boot_storage_acceptance_ready(nvfs)).to_equal(true)
expect(boot_storage_acceptance_reason(nvfs)).to_equal("ready")

val dbfs_result = FsMountResult(
    mounted: true,
    fs_type: FsMountType.Dbfs,
    provider: "simple-driver",
    pure_simple: true
)
val dbfs = ready_boot_storage_evidence(dbfs_result)
expect(boot_storage_acceptance_ready(dbfs)).to_equal(true)

val fat32_result = FsMountResult(
    mounted: true,
    fs_type: FsMountType.Fat32,
    provider: "simple-driver",
    pure_simple: true
)
val fat32 = ready_boot_storage_evidence(fat32_result)
expect(boot_storage_acceptance_ready(fat32)).to_equal(true)
```

</details>

#### uses one provider-neutral BlockDevice entry point for freestanding probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_dev = MemBlockDevice.new(8u64, 512u32)
val result = boot_fs_mount_from_device(empty_dev, "simple-driver", true)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("boot-fs-mount: no root filesystem on provider:simple-driver")
```

</details>

#### mounts FAT32 through the same provider-neutral BlockDevice path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(2048u64, 512u32)
expect(dev.write_sector(0u64, fat32_boot_sector()).is_ok()).to_equal(true)
val result = boot_fs_mount_from_device(dev, "simple-driver", true)
expect(result.is_ok()).to_equal(true)
val mounted = result.unwrap()
expect(mounted.fs_type).to_equal(FsMountType.Fat32)
expect(mounted.provider).to_equal("simple-driver")
expect(mounted.pure_simple).to_equal(true)
```

</details>

#### gates pure NVMe freestanding probing on transfer evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_dev = MemBlockDevice.new(8u64, 512u32)
val missing_sector = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
val rejected = boot_fs_mount_pure_nvme_from_device(empty_dev, missing_sector)
expect(rejected.is_err()).to_equal(true)
expect(rejected.unwrap_err()).to_equal("boot-fs-mount: pure-nvme-adapter-not-ready:missing-nvme-sector-read")

val ready = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
val no_fs = boot_fs_mount_pure_nvme_from_device(empty_dev, ready)
expect(no_fs.is_err()).to_equal(true)
expect(no_fs.unwrap_err()).to_equal("boot-fs-mount: no root filesystem on provider:simple-driver")
```

</details>

#### requires a filesystem-ready NVMe lease before freestanding root probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev = MemBlockDevice.new(2048u64, 512u32)
expect(dev.write_sector(0u64, fat32_boot_sector()).is_ok()).to_equal(true)
val lease = ready_boot_lease("simple-driver")
val invalid = ready_boot_lease("c-boot-bridge")

expect(boot_fs_mount_lease_acceptance_reason(lease)).to_equal("ready")
expect(boot_fs_mount_lease_acceptance_reason(invalid)).to_equal("fat32:nvme-fs-provider-not-simple:c-boot-bridge")

val rejected = boot_fs_mount_pure_nvme_from_lease_device(dev, ready_transfer_evidence(), invalid)
expect(rejected.unwrap_err()).to_equal("boot-fs-mount: nvme-lease-not-ready:fat32:nvme-fs-provider-not-simple:c-boot-bridge")

val mounted = boot_fs_mount_pure_nvme_from_lease_device(dev, ready_transfer_evidence(), lease).unwrap()
expect(mounted.fs_type).to_equal(FsMountType.Fat32)
expect(mounted.provider).to_equal("simple-driver")
expect(mounted.pure_simple).to_equal(true)
```

</details>

#### production freestanding entry consumes provisioned pure NVMe lease device

1. boot fs mount clear production nvme lease device
   - Expected: dev.write_sector(0u64, fat32_boot_sector()).is_ok() is true
2. boot fs mount provision production nvme lease device
   - Expected: mounted.fs_type equals `FsMountType.Fat32`
   - Expected: mounted.provider equals `simple-driver`
   - Expected: mounted.pure_simple is true
3. boot fs mount clear production nvme lease device


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
boot_fs_mount_clear_production_nvme_lease_device()
val dev = MemBlockDevice.new(2048u64, 512u32)
expect(dev.write_sector(0u64, fat32_boot_sector()).is_ok()).to_equal(true)
val lease = ready_boot_lease("simple-driver")
boot_fs_mount_provision_production_nvme_lease_device(dev, ready_transfer_evidence(), lease)

val mounted = boot_fs_mount_freestanding_production().unwrap()
expect(mounted.fs_type).to_equal(FsMountType.Fat32)
expect(mounted.provider).to_equal("simple-driver")
expect(mounted.pure_simple).to_equal(true)
boot_fs_mount_clear_production_nvme_lease_device()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- boot filesystem mount acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
