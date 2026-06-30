# Nvme Namespace Assignment Specification

## Scenarios

### NVMe user namespace assignment

#### mints FAT32 NVFS and DBFS leases from a tokenized user-space DeviceGrant

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val fat = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Fat32).unwrap()
val nvfs = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Nvfs).unwrap()
val dbfs = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Dbfs).unwrap()

expect(fat.queue.role).to_equal(NvmeQueueRole.Data)
expect(fat.queue.owner_task).to_equal(42u64)
expect(fat.grant_kind.to_start_with("resource-grant-set:tok=")).to_equal(true)
expect(nvme_filesystem_lease_ready(fat, NvmeFilesystemConsumer.Fat32)).to_equal(true)
expect(nvme_filesystem_lease_ready(nvfs, NvmeFilesystemConsumer.Nvfs)).to_equal(true)
expect(nvme_filesystem_lease_ready(dbfs, NvmeFilesystemConsumer.Dbfs)).to_equal(true)
```

</details>

#### rejects missing grant tokens before filesystem leases are exposed

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = new_device_grant()
val evidence = nvme_transfer_evidence(
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
    "resource-grant-set:missing",
    "non-secure-resource-namespace",
    true,
    true
)
val result = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Fat32)
expect(result.unwrap_err()).to_equal("nvme-user-namespace-grant-missing-resource-tokens")
```

</details>

#### rejects user namespace owners that do not match the issued DeviceGrant

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val result = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 43u64, 64u16, NvmeFilesystemConsumer.Fat32)
expect(result.unwrap_err()).to_equal("nvme-user-namespace-grant-owner-mismatch")
```

</details>

#### rejects evidence that was not produced for the issued grant

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val other_grant = _grant(43u64)
val evidence = _user_evidence(other_grant)
val result = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
expect(result.unwrap_err()).to_contain("nvme-user-namespace-evidence-grant-mismatch:")
```

</details>

#### uses data queue assignments for user namespace queues

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val queue = nvme_user_namespace_queue_assignment(0u32, 7u32, nvme_first_data_queue_id(), 99u64, 128u16)
expect(queue.role).to_equal(NvmeQueueRole.Data)
expect(queue.owner_task).to_equal(99u64)
```

</details>

#### rejects checked user namespace assignment when boot owns the same namespace

<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val ns = NvmeNamespaceIdentity(
    controller_id: 0,
    nsid: 5,
    lba_size: 4096,
    lba_count: 8192,
    eui64: 0,
    nguid_lo: 0,
    nguid_hi: 0,
    uuid_lo: 0,
    uuid_hi: 0
)
val system_queue = NvmeQueueAssignment(
    queue_id: SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    role: NvmeQueueRole.System,
    controller_id: 0,
    nsid: 5,
    owner_task: 0,
    max_depth: 128,
    rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_QUEUE_SUBMIT
)
val boot_lease = nvme_filesystem_lease(ns, 0u64, 8192u64, NvmeNamespaceMode.System, system_queue, "simple-driver", "kernel-owned-resource", true, true)
val result = nvme_user_assigned_filesystem_lease_from_grant_checked(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Fat32, [boot_lease])

expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("nvme-fs-namespace-mode-conflict:system:user-assigned")
```

</details>

#### accepts checked user namespace assignment for a namespace not owned by boot

<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val ns = NvmeNamespaceIdentity(
    controller_id: 0,
    nsid: 1,
    lba_size: 4096,
    lba_count: 8192,
    eui64: 0,
    nguid_lo: 0,
    nguid_hi: 0,
    uuid_lo: 0,
    uuid_hi: 0
)
val system_queue = NvmeQueueAssignment(
    queue_id: SIMPLEOS_NVME_SYSTEM_QUEUE_ID,
    role: NvmeQueueRole.System,
    controller_id: 0,
    nsid: 1,
    owner_task: 0,
    max_depth: 128,
    rights: CAP_RIGHT_READ + CAP_RIGHT_WRITE + CAP_RIGHT_QUEUE_SUBMIT
)
val boot_lease = nvme_filesystem_lease(ns, 0u64, 8192u64, NvmeNamespaceMode.System, system_queue, "simple-driver", "kernel-owned-resource", true, true)
val result = nvme_user_assigned_filesystem_lease_from_grant_checked(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Dbfs, [boot_lease])

expect(result.is_ok()).to_equal(true)
expect(nvme_filesystem_lease_ready(result.unwrap(), NvmeFilesystemConsumer.Dbfs)).to_equal(true)
```

</details>

#### rejects same queue user leases with different LBA windows

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val active = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Fat32).unwrap()
val same = nvme_user_assigned_filesystem_lease_from_grant_checked(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Nvfs, [active])
val shifted = nvme_user_assigned_filesystem_lease_from_grant_checked(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 256u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Dbfs, [active])
val resized = nvme_user_assigned_filesystem_lease_from_grant_checked(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 2048u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Dbfs, [active])

expect(same.is_ok()).to_equal(true)
expect(nvme_filesystem_lease_same_identity(active, same.unwrap())).to_equal(true)
expect(shifted.unwrap_err()).to_equal("nvme-fs-user-namespace-window-conflict")
expect(resized.unwrap_err()).to_equal("nvme-fs-user-namespace-window-conflict")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe user namespace assignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

