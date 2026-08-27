# Nvme Namespace Assignment Specification

> Tests covering NVMe user namespace assignment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Namespace Assignment Specification

## Scenarios

### NVMe user namespace assignment

#### mints FAT32 NVFS and DBFS leases from a tokenized user-space DeviceGrant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mints FAT32 NVFS and DBFS leases from a tokenized user-space DeviceGrant
   - Expected: fat.queue.role equals `NvmeQueueRole.Data`
   - Expected: fat.queue.owner_task equals `42u64`
   - Expected: fat.grant_kind.to_start_with("resource-grant-set:tok=") is true
   - Expected: nvme_filesystem_lease_ready(fat, NvmeFilesystemConsumer.Fat32) is true
   - Expected: nvme_filesystem_lease_ready(nvfs, NvmeFilesystemConsumer.Nvfs) is true
   - Expected: nvme_filesystem_lease_ready(dbfs, NvmeFilesystemConsumer.Dbfs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mints FAT32 NVFS and DBFS leases from a tokenized user-space DeviceGrant")
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

- rejects missing grant tokens before filesystem leases are exposed
   - Expected: result.unwrap_err() equals `nvme-user-namespace-grant-missing-resource-tokens`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects missing grant tokens before filesystem leases are exposed")
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

- rejects user namespace owners that do not match the issued DeviceGrant
   - Expected: result.unwrap_err() equals `nvme-user-namespace-grant-owner-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects user namespace owners that do not match the issued DeviceGrant")
val grant = _grant(42u64)
val evidence = _user_evidence(grant)
val result = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 43u64, 64u16, NvmeFilesystemConsumer.Fat32)
expect(result.unwrap_err()).to_equal("nvme-user-namespace-grant-owner-mismatch")
```

</details>

#### rejects evidence that was not produced for the issued grant

- rejects evidence that was not produced for the issued grant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects evidence that was not produced for the issued grant")
val grant = _grant(42u64)
val other_grant = _grant(43u64)
val evidence = _user_evidence(other_grant)
val result = nvme_user_assigned_filesystem_lease_from_grant(evidence, grant, 0u32, 5u32, 4096u32, 8192u64, 128u64, 1024u64, nvme_first_data_queue_id(), 42u64, 64u16, NvmeFilesystemConsumer.Nvfs)
expect(result.unwrap_err()).to_contain("nvme-user-namespace-evidence-grant-mismatch:")
```

</details>

#### uses data queue assignments for user namespace queues

- uses data queue assignments for user namespace queues
   - Expected: queue.role equals `NvmeQueueRole.Data`
   - Expected: queue.owner_task equals `99u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses data queue assignments for user namespace queues")
val queue = nvme_user_namespace_queue_assignment(0u32, 7u32, nvme_first_data_queue_id(), 99u64, 128u16)
expect(queue.role).to_equal(NvmeQueueRole.Data)
expect(queue.owner_task).to_equal(99u64)
```

</details>

#### rejects checked user namespace assignment when boot owns the same namespace

- rejects checked user namespace assignment when boot owns the same namespace
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `nvme-fs-namespace-mode-conflict:system:user-assigned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects checked user namespace assignment when boot owns the same namespace")
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

- accepts checked user namespace assignment for a namespace not owned by boot
   - Expected: result.is_ok() is true
   - Expected: nvme_filesystem_lease_ready(result.unwrap(), NvmeFilesystemConsumer.Dbfs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts checked user namespace assignment for a namespace not owned by boot")
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

- rejects same queue user leases with different LBA windows
   - Expected: same.is_ok() is true
   - Expected: nvme_filesystem_lease_same_identity(active, same.unwrap()) is true
   - Expected: shifted.unwrap_err() equals `nvme-fs-user-namespace-window-conflict`
   - Expected: resized.unwrap_err() equals `nvme-fs-user-namespace-window-conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects same queue user leases with different LBA windows")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe user namespace assignment.
- NVMe user namespace assignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `1e04965ca35fcef3594e5ff9bb7b656b98f7e7885c7fe5f35abe7d3ef1392b96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e04965ca35fcef3594e5ff9bb7b656b98f7e7885c7fe5f35abe7d3ef1392b96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e04965ca35fcef3594e5ff9bb7b656b98f7e7885c7fe5f35abe7d3ef1392b96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/nvme/nvme_namespace_assignment_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses data queue assignments for user namespace queues' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
