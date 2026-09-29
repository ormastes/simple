# Boot Fs Mount Acceptance Specification

> Tests covering boot filesystem mount acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Fs Mount Acceptance Specification

## Scenarios

### boot filesystem mount acceptance

#### default and production freestanding entries require provisioned pure NVMe lease device

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default and production freestanding entries require provisioned pure NVMe lease device
   - Expected: default_rejected.is_err() is true
   - Expected: default_rejected.unwrap_err() equals `boot-fs-mount: pure-nvme-production-device-not-provisioned`
   - Expected: rejected.is_err() is true
   - Expected: rejected.unwrap_err() equals `boot-fs-mount: pure-nvme-production-device-not-provisioned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default and production freestanding entries require provisioned pure NVMe lease device")
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

- rejects C bridge mounts as pure Simple boot storage
   - Expected: boot_fs_mount_acceptance_reason(c_bridge) equals `boot-storage-not-pure-simple:c-boot-bridge`
   - Expected: boot_fs_mount_provider_is_pure_simple("c-boot-bridge") is false
   - Expected: boot_fs_mount_provider_is_pure_simple("simple-driver") is true
   - Expected: boot_storage_acceptance_ready(evidence) is false
   - Expected: boot_storage_acceptance_reason(evidence) equals `boot-storage-not-pure-simple:c-boot-bridge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects C bridge mounts as pure Simple boot storage")
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

- requires PCI grants, transfers, sector probe, and non-secure namespace
   - Expected: boot_storage_acceptance_reason(missing_grant) equals `missing-boot-storage-pci-grant`
   - Expected: boot_storage_acceptance_reason(missing_transfer) equals `missing-boot-storage-transfer`
   - Expected: boot_storage_acceptance_reason(missing_probe) equals `missing-real-sector-superblock-probe`
   - Expected: boot_storage_acceptance_reason(secure_namespace) equals `missing-boot-storage-non-secure-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires PCI grants, transfers, sector probe, and non-secure namespace")
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

- requires direct-access grant placement shared logic and broker evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires direct-access grant placement shared logic and broker evidence")
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

- accepts NVFS DBFS and FAT32 only after the full Simple evidence set
   - Expected: boot_storage_acceptance_ready(nvfs) is true
   - Expected: boot_storage_acceptance_reason(nvfs) equals `ready`
   - Expected: boot_storage_acceptance_ready(dbfs) is true
   - Expected: boot_storage_acceptance_ready(fat32) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts NVFS DBFS and FAT32 only after the full Simple evidence set")
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

- uses one provider-neutral BlockDevice entry point for freestanding probes
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `boot-fs-mount: no root filesystem on provider:simple-driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses one provider-neutral BlockDevice entry point for freestanding probes")
val empty_dev = MemBlockDevice.new(8u64, 512u32)
val result = boot_fs_mount_from_device(empty_dev, "simple-driver", true)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("boot-fs-mount: no root filesystem on provider:simple-driver")
```

</details>

#### mounts FAT32 through the same provider-neutral BlockDevice path

- mounts FAT32 through the same provider-neutral BlockDevice path
   - Expected: dev.write_sector(0u64, fat32_boot_sector()).is_ok() is true
   - Expected: result.is_ok() is true
   - Expected: mounted.fs_type equals `FsMountType.Fat32`
   - Expected: mounted.provider equals `simple-driver`
   - Expected: mounted.pure_simple is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mounts FAT32 through the same provider-neutral BlockDevice path")
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

- gates pure NVMe freestanding probing on transfer evidence
   - Expected: rejected.is_err() is true
   - Expected: rejected.unwrap_err() equals `boot-fs-mount: pure-nvme-adapter-not-ready:missing-nvme-sector-read`
   - Expected: no_fs.is_err() is true
   - Expected: no_fs.unwrap_err() equals `boot-fs-mount: no root filesystem on provider:simple-driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates pure NVMe freestanding probing on transfer evidence")
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

- requires a filesystem-ready NVMe lease before freestanding root probes
   - Expected: dev.write_sector(0u64, fat32_boot_sector()).is_ok() is true
   - Expected: boot_fs_mount_lease_acceptance_reason(lease) equals `ready`
   - Expected: boot_fs_mount_lease_acceptance_reason(invalid) equals `fat32:nvme-fs-provider-not-simple:c-boot-bridge`
   - Expected: rejected.unwrap_err() equals `boot-fs-mount: nvme-lease-not-ready:fat32:nvme-fs-provider-not-simple:c-boot-... (full value in folded executable source)`
   - Expected: mounted.fs_type equals `FsMountType.Fat32`
   - Expected: mounted.provider equals `simple-driver`
   - Expected: mounted.pure_simple is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a filesystem-ready NVMe lease before freestanding root probes")
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

- production freestanding entry consumes provisioned pure NVMe lease device
   - Expected: dev.write_sector(0u64, fat32_boot_sector()).is_ok() is true
   - Expected: mounted.fs_type equals `FsMountType.Fat32`
   - Expected: mounted.provider equals `simple-driver`
   - Expected: mounted.pure_simple is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("production freestanding entry consumes provisioned pure NVMe lease device")
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
| Source | `test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering boot filesystem mount acceptance.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83b9a46e643b9f8b2d6518f92d43957c39aa8e1f560899e033795e3ce15d16e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83b9a46e643b9f8b2d6518f92d43957c39aa8e1f560899e033795e3ce15d16e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83b9a46e643b9f8b2d6518f92d43957c39aa8e1f560899e033795e3ce15d16e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl
mirror: doc/06_spec/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default and production freestanding entries require provisioned pure NVMe lease device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl:310:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses one provider-neutral BlockDevice entry point for freestanding probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/boot/boot_fs_mount_acceptance_spec.spl:318:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mounts FAT32 through the same provider-neutral BlockDevice path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
